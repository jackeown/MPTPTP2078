%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S71DisEZ9P

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  81 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  287 ( 705 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t91_mcart_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) )
            & ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_mcart_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( ( ( k3_xboole_0 @ X23 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X23 ) @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('3',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X9 ) )
      | ( r2_hidden @ X6 @ X9 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('16',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( $false
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','16'])).

thf('18',plain,(
    r2_hidden @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('20',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['17','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S71DisEZ9P
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 43 iterations in 0.027s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(t91_mcart_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( r2_hidden @ B @ A ) =>
% 0.21/0.48           ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.48             ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( r2_hidden @ B @ A ) =>
% 0.21/0.48              ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.48                ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t91_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.21/0.48        | ~ (r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))
% 0.21/0.48         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(t22_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k3_xboole_0 @
% 0.21/0.48           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.21/0.48         ( A ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X23 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X23 @ 
% 0.21/0.48            (k2_zfmisc_1 @ (k1_relat_1 @ X23) @ (k2_relat_1 @ X23))) = (
% 0.21/0.48            X23))
% 0.21/0.48          | ~ (v1_relat_1 @ X23))),
% 0.21/0.48      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.48  thf('3', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t1_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.48       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.48         ((r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X9))
% 0.21/0.48          | (r2_hidden @ X6 @ X9)
% 0.21/0.48          | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ sk_B @ X0)
% 0.21/0.48          | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf(l98_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k5_xboole_0 @ A @ B ) =
% 0.21/0.48       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         ((k5_xboole_0 @ X10 @ X11)
% 0.21/0.48           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.21/0.48              (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.21/0.48  thf(d5_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.48          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.48          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.48          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.21/0.48          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ sk_B @ X0)
% 0.21/0.48          | ~ (r2_hidden @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | (r2_hidden @ sk_B @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '10'])).
% 0.21/0.48  thf('12', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((r2_hidden @ sk_B @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.48  thf(t10_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.48         ((r2_hidden @ (k2_mcart_1 @ X24) @ X26)
% 0.21/0.48          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.48  thf('16', plain, ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (($false)
% 0.21/0.48         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['1', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((r2_hidden @ sk_B @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_mcart_1 @ X24) @ X25)
% 0.21/0.48          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.48  thf('20', plain, ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((~ (r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))
% 0.21/0.48         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('22', plain, (((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))) | 
% 0.21/0.48       ~ ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, ($false),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['17', '24'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
