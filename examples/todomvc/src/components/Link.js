import React from 'react'
import PropTypes from 'prop-types'
import classnames from 'classnames'

const Link = ({ active, children, setFilter }) =>
  (
    // eslint-disable-next-line jsx-a11y/anchor-is-valid
    <a
      className={classnames({ selected: active })}
      style={{ cursor: 'pointer' }}
      onClick={() => setFilter()}
    >
      {children}
    </a>
  )

export default Link
