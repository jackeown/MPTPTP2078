%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oFpU0sKhfk

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:04 EST 2020

% Result     : Theorem 12.31s
% Output     : Refutation 12.31s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 101 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  384 ( 783 expanded)
%              Number of equality atoms :   40 (  87 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X27: $i,X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X27 @ X29 ) @ X30 )
        = ( k2_tarski @ X27 @ X29 ) )
      | ( r2_hidden @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','28'])).

thf('30',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oFpU0sKhfk
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 12.31/12.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.31/12.52  % Solved by: fo/fo7.sh
% 12.31/12.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.31/12.52  % done 13483 iterations in 12.051s
% 12.31/12.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.31/12.52  % SZS output start Refutation
% 12.31/12.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.31/12.52  thf(sk_C_type, type, sk_C: $i).
% 12.31/12.52  thf(sk_A_type, type, sk_A: $i).
% 12.31/12.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.31/12.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.31/12.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.31/12.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.31/12.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.31/12.52  thf(sk_B_type, type, sk_B: $i).
% 12.31/12.52  thf(t144_zfmisc_1, conjecture,
% 12.31/12.52    (![A:$i,B:$i,C:$i]:
% 12.31/12.52     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 12.31/12.52          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 12.31/12.52  thf(zf_stmt_0, negated_conjecture,
% 12.31/12.52    (~( ![A:$i,B:$i,C:$i]:
% 12.31/12.52        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 12.31/12.52             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 12.31/12.52    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 12.31/12.52  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 12.31/12.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.31/12.52  thf(t72_zfmisc_1, axiom,
% 12.31/12.52    (![A:$i,B:$i,C:$i]:
% 12.31/12.52     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 12.31/12.52       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 12.31/12.52  thf('1', plain,
% 12.31/12.52      (![X27 : $i, X29 : $i, X30 : $i]:
% 12.31/12.52         (((k4_xboole_0 @ (k2_tarski @ X27 @ X29) @ X30)
% 12.31/12.52            = (k2_tarski @ X27 @ X29))
% 12.31/12.52          | (r2_hidden @ X29 @ X30)
% 12.31/12.52          | (r2_hidden @ X27 @ X30))),
% 12.31/12.52      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 12.31/12.52  thf(t3_boole, axiom,
% 12.31/12.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 12.31/12.52  thf('2', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 12.31/12.52      inference('cnf', [status(esa)], [t3_boole])).
% 12.31/12.52  thf(t48_xboole_1, axiom,
% 12.31/12.52    (![A:$i,B:$i]:
% 12.31/12.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 12.31/12.52  thf('3', plain,
% 12.31/12.52      (![X13 : $i, X14 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.31/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.31/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.31/12.52  thf('4', plain,
% 12.31/12.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 12.31/12.52      inference('sup+', [status(thm)], ['2', '3'])).
% 12.31/12.52  thf(t47_xboole_1, axiom,
% 12.31/12.52    (![A:$i,B:$i]:
% 12.31/12.52     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 12.31/12.52  thf('5', plain,
% 12.31/12.52      (![X11 : $i, X12 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 12.31/12.52           = (k4_xboole_0 @ X11 @ X12))),
% 12.31/12.52      inference('cnf', [status(esa)], [t47_xboole_1])).
% 12.31/12.52  thf('6', plain,
% 12.31/12.52      (![X0 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 12.31/12.52           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 12.31/12.52      inference('sup+', [status(thm)], ['4', '5'])).
% 12.31/12.52  thf('7', plain,
% 12.31/12.52      (![X13 : $i, X14 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.31/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.31/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.31/12.52  thf('8', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 12.31/12.52      inference('cnf', [status(esa)], [t3_boole])).
% 12.31/12.52  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 12.31/12.52      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.31/12.52  thf(t52_xboole_1, axiom,
% 12.31/12.52    (![A:$i,B:$i,C:$i]:
% 12.31/12.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 12.31/12.52       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 12.31/12.52  thf('10', plain,
% 12.31/12.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 12.31/12.52           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 12.31/12.52              (k3_xboole_0 @ X18 @ X20)))),
% 12.31/12.52      inference('cnf', [status(esa)], [t52_xboole_1])).
% 12.31/12.52  thf('11', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 12.31/12.52           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 12.31/12.52      inference('sup+', [status(thm)], ['9', '10'])).
% 12.31/12.52  thf(commutativity_k2_xboole_0, axiom,
% 12.31/12.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 12.31/12.52  thf('12', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.31/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.31/12.52  thf('13', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 12.31/12.52           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 12.31/12.52      inference('demod', [status(thm)], ['11', '12'])).
% 12.31/12.52  thf('14', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 12.31/12.52           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 12.31/12.52      inference('demod', [status(thm)], ['11', '12'])).
% 12.31/12.52  thf('15', plain,
% 12.31/12.52      (![X13 : $i, X14 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.31/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.31/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.31/12.52  thf('16', plain,
% 12.31/12.52      (![X13 : $i, X14 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.31/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.31/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.31/12.52  thf('17', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 12.31/12.52           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.31/12.52      inference('sup+', [status(thm)], ['15', '16'])).
% 12.31/12.52  thf('18', plain,
% 12.31/12.52      (![X11 : $i, X12 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 12.31/12.52           = (k4_xboole_0 @ X11 @ X12))),
% 12.31/12.52      inference('cnf', [status(esa)], [t47_xboole_1])).
% 12.31/12.52  thf('19', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X1 @ X0)
% 12.31/12.52           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.31/12.52      inference('demod', [status(thm)], ['17', '18'])).
% 12.31/12.52  thf('20', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 12.31/12.52           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 12.31/12.52      inference('sup+', [status(thm)], ['14', '19'])).
% 12.31/12.52  thf('21', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 12.31/12.52           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 12.31/12.52      inference('demod', [status(thm)], ['11', '12'])).
% 12.31/12.52  thf(t46_xboole_1, axiom,
% 12.31/12.52    (![A:$i,B:$i]:
% 12.31/12.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 12.31/12.52  thf('22', plain,
% 12.31/12.52      (![X9 : $i, X10 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 12.31/12.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 12.31/12.52  thf('23', plain,
% 12.31/12.52      (![X13 : $i, X14 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.31/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.31/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.31/12.52  thf('24', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 12.31/12.52           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.31/12.52      inference('sup+', [status(thm)], ['22', '23'])).
% 12.31/12.52  thf('25', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 12.31/12.52      inference('cnf', [status(esa)], [t3_boole])).
% 12.31/12.52  thf('26', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.31/12.52      inference('demod', [status(thm)], ['24', '25'])).
% 12.31/12.52  thf('27', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 12.31/12.52      inference('demod', [status(thm)], ['20', '21', '26'])).
% 12.31/12.52  thf('28', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i]:
% 12.31/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 12.31/12.52      inference('demod', [status(thm)], ['13', '27'])).
% 12.31/12.52  thf('29', plain,
% 12.31/12.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.31/12.52         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2))
% 12.31/12.52          | (r2_hidden @ X1 @ X2)
% 12.31/12.52          | (r2_hidden @ X0 @ X2))),
% 12.31/12.52      inference('sup+', [status(thm)], ['1', '28'])).
% 12.31/12.52  thf('30', plain,
% 12.31/12.52      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 12.31/12.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.31/12.52  thf('31', plain,
% 12.31/12.52      ((((sk_C) != (sk_C))
% 12.31/12.52        | (r2_hidden @ sk_B @ sk_C)
% 12.31/12.52        | (r2_hidden @ sk_A @ sk_C))),
% 12.31/12.52      inference('sup-', [status(thm)], ['29', '30'])).
% 12.31/12.52  thf('32', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 12.31/12.52      inference('simplify', [status(thm)], ['31'])).
% 12.31/12.52  thf('33', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 12.31/12.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.31/12.52  thf('34', plain, ((r2_hidden @ sk_B @ sk_C)),
% 12.31/12.52      inference('clc', [status(thm)], ['32', '33'])).
% 12.31/12.52  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 12.31/12.52  
% 12.31/12.52  % SZS output end Refutation
% 12.31/12.52  
% 12.31/12.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
