%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.986XLmrrWE

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:06 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   61 (  91 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  380 ( 617 expanded)
%              Number of equality atoms :   42 (  70 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X21 @ X23 ) @ X24 )
        = ( k2_tarski @ X21 @ X23 ) )
      | ( r2_hidden @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','33'])).

thf('35',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.986XLmrrWE
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.59/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.85  % Solved by: fo/fo7.sh
% 0.59/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.85  % done 1095 iterations in 0.389s
% 0.59/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.85  % SZS output start Refutation
% 0.59/0.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.85  thf(t144_zfmisc_1, conjecture,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.59/0.85          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.59/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.85        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.59/0.85             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.59/0.85    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.59/0.85  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(t72_zfmisc_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.59/0.85       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.59/0.85  thf('1', plain,
% 0.59/0.85      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.59/0.85         (((k4_xboole_0 @ (k2_tarski @ X21 @ X23) @ X24)
% 0.59/0.85            = (k2_tarski @ X21 @ X23))
% 0.59/0.85          | (r2_hidden @ X23 @ X24)
% 0.59/0.85          | (r2_hidden @ X21 @ X24))),
% 0.59/0.85      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.59/0.85  thf(t48_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.85  thf('2', plain,
% 0.59/0.85      (![X11 : $i, X12 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.59/0.85           = (k3_xboole_0 @ X11 @ X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.85  thf(t36_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.85  thf('3', plain,
% 0.59/0.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.59/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.85  thf('4', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.59/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.59/0.85  thf(l32_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.85  thf('5', plain,
% 0.59/0.85      (![X3 : $i, X5 : $i]:
% 0.59/0.85         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.85      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.85  thf('6', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.85  thf(t49_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.59/0.85       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.59/0.85  thf('7', plain,
% 0.59/0.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.85         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.59/0.85           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.59/0.85      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.59/0.85  thf(t100_xboole_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.85  thf('8', plain,
% 0.59/0.85      (![X6 : $i, X7 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X6 @ X7)
% 0.59/0.85           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.85  thf('9', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.85           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 0.59/0.85      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.85  thf('10', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.85           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['6', '9'])).
% 0.59/0.85  thf(t3_boole, axiom,
% 0.59/0.85    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.85  thf('11', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.59/0.85      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.85  thf('12', plain,
% 0.59/0.85      (![X11 : $i, X12 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.59/0.85           = (k3_xboole_0 @ X11 @ X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.85  thf('13', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.85  thf(d10_xboole_0, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.85  thf('14', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.59/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.85  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.85      inference('simplify', [status(thm)], ['14'])).
% 0.59/0.85  thf('16', plain,
% 0.59/0.85      (![X3 : $i, X5 : $i]:
% 0.59/0.85         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.85      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.85  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.85  thf('18', plain,
% 0.59/0.85      (![X11 : $i, X12 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.59/0.85           = (k3_xboole_0 @ X11 @ X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.85  thf('19', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.85  thf('20', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.59/0.85      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.85  thf('21', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.85  thf('22', plain,
% 0.59/0.85      (![X6 : $i, X7 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X6 @ X7)
% 0.59/0.85           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.85  thf('23', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.85  thf('24', plain,
% 0.59/0.85      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.85      inference('demod', [status(thm)], ['13', '23'])).
% 0.59/0.85  thf('25', plain,
% 0.59/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.85  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.85  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['25', '26'])).
% 0.59/0.85  thf('28', plain,
% 0.59/0.85      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['24', '27'])).
% 0.59/0.85  thf('29', plain,
% 0.59/0.85      (![X6 : $i, X7 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X6 @ X7)
% 0.59/0.85           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.85  thf('30', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['28', '29'])).
% 0.59/0.85  thf('31', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.59/0.85      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.85  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['30', '31'])).
% 0.59/0.85  thf('33', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.59/0.85      inference('demod', [status(thm)], ['10', '32'])).
% 0.59/0.85  thf('34', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.85         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2))
% 0.59/0.85          | (r2_hidden @ X1 @ X2)
% 0.59/0.85          | (r2_hidden @ X0 @ X2))),
% 0.59/0.85      inference('sup+', [status(thm)], ['1', '33'])).
% 0.59/0.85  thf('35', plain,
% 0.59/0.85      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('36', plain,
% 0.59/0.85      ((((sk_C) != (sk_C))
% 0.59/0.85        | (r2_hidden @ sk_B @ sk_C)
% 0.59/0.85        | (r2_hidden @ sk_A @ sk_C))),
% 0.59/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.85  thf('37', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.59/0.85      inference('simplify', [status(thm)], ['36'])).
% 0.59/0.85  thf('38', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('39', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.59/0.85      inference('clc', [status(thm)], ['37', '38'])).
% 0.59/0.85  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.59/0.85  
% 0.59/0.85  % SZS output end Refutation
% 0.59/0.85  
% 0.69/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
