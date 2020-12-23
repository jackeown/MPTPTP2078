%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2Q3QGv5pP

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  83 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  358 ( 855 expanded)
%              Number of equality atoms :   32 (  78 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t16_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X2 ) @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X2 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('5',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7
       != ( k4_tarski @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ X7 ) @ X9 )
      | ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t11_mcart_1])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X5 @ X6 ) ) @ X9 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ X6 @ X9 )
      | ~ ( r2_hidden @ X5 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_mcart_1 @ X11 )
        = X10 )
      | ( ( k1_mcart_1 @ X11 )
        = X12 )
      | ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ ( k2_tarski @ X12 @ X10 ) @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_C )
    | ( ( k1_mcart_1 @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('25',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['19','25'])).

thf('27',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['21'])).

thf('28',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('29',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['23','28'])).

thf('30',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','26','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2Q3QGv5pP
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 24 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.47  thf(t16_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.47         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.47          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.47            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t16_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t10_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((r2_hidden @ (k2_mcart_1 @ X2) @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X3 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_mcart_1 @ X2) @ X3)
% 0.20/0.47          | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X3 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.47  thf('5', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf(t11_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.20/0.47       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.20/0.47         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (((X7) != (k4_tarski @ X5 @ X6))
% 0.20/0.47          | ~ (r2_hidden @ (k1_mcart_1 @ X7) @ X8)
% 0.20/0.47          | ~ (r2_hidden @ (k2_mcart_1 @ X7) @ X9)
% 0.20/0.47          | (r2_hidden @ X7 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t11_mcart_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         ((r2_hidden @ (k4_tarski @ X5 @ X6) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.47          | ~ (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X5 @ X6)) @ X9)
% 0.20/0.47          | ~ (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X5 @ X6)) @ X8))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf(t7_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.47       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         ((r2_hidden @ (k4_tarski @ X5 @ X6) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.47          | ~ (r2_hidden @ X6 @ X9)
% 0.20/0.47          | ~ (r2_hidden @ X5 @ X8))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.47             (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((r2_hidden @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.47        (k2_zfmisc_1 @ (k2_tarski @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '11'])).
% 0.20/0.47  thf(t15_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.20/0.47       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         (((k1_mcart_1 @ X11) = (X10))
% 0.20/0.47          | ((k1_mcart_1 @ X11) = (X12))
% 0.20/0.47          | ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ (k2_tarski @ X12 @ X10) @ X13)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((((k1_mcart_1 @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)))
% 0.20/0.47          = (sk_C))
% 0.20/0.47        | ((k1_mcart_1 @ 
% 0.20/0.47            (k4_tarski @ (k2_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A))) = (
% 0.20/0.47            sk_D)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_A) = (sk_C)) | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.47        | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.47      inference('split', [status(esa)], ['18'])).
% 0.20/0.47  thf('20', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.47        | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.20/0.47         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['21'])).
% 0.20/0.47  thf('23', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | 
% 0.20/0.47       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('split', [status(esa)], ['18'])).
% 0.20/0.47  thf('25', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['19', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['21'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | 
% 0.20/0.48       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('split', [status(esa)], ['21'])).
% 0.20/0.48  thf('29', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['23', '28'])).
% 0.20/0.48  thf('30', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 0.20/0.48  thf('31', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['17', '26', '30'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
