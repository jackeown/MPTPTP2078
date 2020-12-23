%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cKDbXSK2i7

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  83 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  316 ( 759 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('2',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( ( k3_xboole_0 @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['11','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('19',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( $false
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','19'])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['20','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cKDbXSK2i7
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 117 iterations in 0.071s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(t91_mcart_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( r2_hidden @ B @ A ) =>
% 0.20/0.53           ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.53             ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( v1_relat_1 @ A ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( r2_hidden @ B @ A ) =>
% 0.20/0.53              ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.53                ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t91_mcart_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.20/0.53        | ~ (r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))
% 0.20/0.53         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d5_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.53          | (r2_hidden @ X2 @ X4)
% 0.20/0.53          | (r2_hidden @ X2 @ X5)
% 0.20/0.53          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.20/0.53          | (r2_hidden @ X2 @ X4)
% 0.20/0.53          | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ sk_B @ X0)
% 0.20/0.53          | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.53  thf(t22_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ( k3_xboole_0 @
% 0.20/0.53           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.20/0.53         ( A ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X12 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X12 @ 
% 0.20/0.53            (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12))) = (
% 0.20/0.53            X12))
% 0.20/0.53          | ~ (v1_relat_1 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.53  thf(t48_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.53           = (k3_xboole_0 @ X10 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.53          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.53          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.53          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ 
% 0.20/0.53               (k4_xboole_0 @ X0 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.53          | (r2_hidden @ X6 @ X3)
% 0.20/0.53          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.53         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ 
% 0.20/0.53             (k4_xboole_0 @ X0 @ 
% 0.20/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['11', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (((r2_hidden @ sk_B @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '14'])).
% 0.20/0.53  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((r2_hidden @ sk_B @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t10_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.53       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.53         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.20/0.53          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('19', plain, ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (($false)
% 0.20/0.53         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['1', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((r2_hidden @ sk_B @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.20/0.53          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('23', plain, ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))
% 0.20/0.53         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('25', plain, (((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))) | 
% 0.20/0.53       ~ ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain, ($false),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['20', '27'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
