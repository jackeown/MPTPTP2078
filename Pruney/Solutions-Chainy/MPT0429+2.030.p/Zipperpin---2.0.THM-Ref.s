%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.82NRO4DcbE

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  72 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  166 ( 392 expanded)
%              Number of equality atoms :    8 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( r1_xboole_0 @ X4 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('1',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['0'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( m1_subset_1 @ ( k1_tarski @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t61_setfam_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_setfam_1])).

thf('5',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    m1_subset_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['10','13'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['10','13'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.82NRO4DcbE
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:43:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 31 iterations in 0.019s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(t66_xboole_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X4 : $i]: ((r1_xboole_0 @ X4 @ X4) | ((X4) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.48  thf('1', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.48  thf(t4_subset_1, axiom,
% 0.20/0.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.48  thf(t55_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.48       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.48         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X36 : $i, X37 : $i]:
% 0.20/0.48         (((X36) = (k1_xboole_0))
% 0.20/0.48          | ~ (m1_subset_1 @ X37 @ X36)
% 0.20/0.48          | (m1_subset_1 @ (k1_tarski @ X37) @ (k1_zfmisc_1 @ X36)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.20/0.48          | ((k1_zfmisc_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(t61_setfam_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( m1_subset_1 @
% 0.20/0.48       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( m1_subset_1 @
% 0.20/0.48          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, (((k1_zfmisc_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.48  thf('8', plain, ((m1_subset_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(t2_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X38 : $i, X39 : $i]:
% 0.20/0.48         ((r2_hidden @ X38 @ X39)
% 0.20/0.48          | (v1_xboole_0 @ X39)
% 0.20/0.48          | ~ (m1_subset_1 @ X38 @ X39))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, (((k1_zfmisc_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(fc1_subset_1, axiom,
% 0.20/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('12', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.48  thf('13', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('clc', [status(thm)], ['10', '13'])).
% 0.20/0.48  thf(t3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain, (~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '16'])).
% 0.20/0.48  thf('18', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('clc', [status(thm)], ['10', '13'])).
% 0.20/0.48  thf('19', plain, ($false), inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
