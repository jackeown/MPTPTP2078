%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wt6YByTc8Y

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:46 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 118 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  485 ( 799 expanded)
%              Number of equality atoms :   61 ( 104 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X57 ) @ ( k2_tarski @ X57 @ X58 ) )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','29'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('31',plain,(
    ! [X53: $i,X55: $i,X56: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X53 @ X55 ) @ X56 )
        = ( k1_tarski @ X53 ) )
      | ( X53 != X55 )
      | ( r2_hidden @ X53 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('32',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r2_hidden @ X55 @ X56 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X55 @ X55 ) @ X56 )
        = ( k1_tarski @ X55 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r2_hidden @ X55 @ X56 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X55 ) @ X56 )
        = ( k1_tarski @ X55 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('37',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X53 @ X55 ) @ X54 )
       != ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X22 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('40',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X22 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['38','40'])).

thf('42',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(clc,[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X21 )
      | ( X23 = X22 )
      | ( X23 = X19 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('44',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( X23 = X19 )
      | ( X23 = X22 )
      | ~ ( r2_hidden @ X23 @ ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wt6YByTc8Y
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 190 iterations in 0.062s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.52  thf(t28_zfmisc_1, conjecture,
% 0.35/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.52     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.35/0.52          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.52        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.35/0.52             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.35/0.52  thf('0', plain,
% 0.35/0.52      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(t19_zfmisc_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.35/0.52       ( k1_tarski @ A ) ))).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      (![X57 : $i, X58 : $i]:
% 0.35/0.52         ((k3_xboole_0 @ (k1_tarski @ X57) @ (k2_tarski @ X57 @ X58))
% 0.35/0.52           = (k1_tarski @ X57))),
% 0.35/0.52      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.35/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.35/0.52  thf('2', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.52  thf(t17_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.35/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.35/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.35/0.52  thf('5', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 0.35/0.52      inference('sup+', [status(thm)], ['1', '4'])).
% 0.35/0.52  thf(t1_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.35/0.52       ( r1_tarski @ A @ C ) ))).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.52         (~ (r1_tarski @ X10 @ X11)
% 0.35/0.52          | ~ (r1_tarski @ X11 @ X12)
% 0.35/0.52          | (r1_tarski @ X10 @ X12))),
% 0.35/0.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.35/0.52  thf('7', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.35/0.52          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.35/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.52  thf('8', plain,
% 0.35/0.52      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.35/0.52      inference('sup-', [status(thm)], ['0', '7'])).
% 0.35/0.52  thf(t28_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      (![X13 : $i, X14 : $i]:
% 0.35/0.52         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.35/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.35/0.52         = (k1_tarski @ sk_A))),
% 0.35/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.52  thf(t100_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.52  thf('11', plain,
% 0.35/0.52      (![X6 : $i, X7 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.35/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.35/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.52  thf('13', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.35/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.52  thf('14', plain,
% 0.35/0.52      (![X13 : $i, X14 : $i]:
% 0.35/0.52         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.35/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.52  thf('15', plain,
% 0.35/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.52  thf('16', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.52  thf('17', plain,
% 0.35/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.52  thf('18', plain,
% 0.35/0.52      (![X6 : $i, X7 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.52  thf('19', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.35/0.52  thf(t5_boole, axiom,
% 0.35/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.52  thf('20', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.35/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.52  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.52  thf(t48_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.52  thf('22', plain,
% 0.35/0.52      (![X16 : $i, X17 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.35/0.52           = (k3_xboole_0 @ X16 @ X17))),
% 0.35/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.52  thf('23', plain,
% 0.35/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.52  thf('24', plain,
% 0.35/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.52  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.35/0.52  thf('26', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.35/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.35/0.52  thf('27', plain,
% 0.35/0.52      (![X6 : $i, X7 : $i]:
% 0.35/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.52  thf('28', plain,
% 0.35/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.35/0.52  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['25', '28'])).
% 0.35/0.52  thf('30', plain,
% 0.35/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.35/0.53         = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['12', '29'])).
% 0.35/0.53  thf(l38_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.53       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.35/0.53         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X53 : $i, X55 : $i, X56 : $i]:
% 0.35/0.53         (((k4_xboole_0 @ (k2_tarski @ X53 @ X55) @ X56) = (k1_tarski @ X53))
% 0.35/0.53          | ((X53) != (X55))
% 0.35/0.53          | (r2_hidden @ X53 @ X56))),
% 0.35/0.53      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X55 : $i, X56 : $i]:
% 0.35/0.53         ((r2_hidden @ X55 @ X56)
% 0.35/0.53          | ((k4_xboole_0 @ (k2_tarski @ X55 @ X55) @ X56) = (k1_tarski @ X55)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.35/0.53  thf(t69_enumset1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X55 : $i, X56 : $i]:
% 0.35/0.53         ((r2_hidden @ X55 @ X56)
% 0.35/0.53          | ((k4_xboole_0 @ (k1_tarski @ X55) @ X56) = (k1_tarski @ X55)))),
% 0.35/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.35/0.53        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['30', '34'])).
% 0.35/0.53  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X53 @ X54)
% 0.35/0.53          | ((k4_xboole_0 @ (k2_tarski @ X53 @ X55) @ X54) != (k1_tarski @ X53)))),
% 0.35/0.53      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.35/0.53          | ~ (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.53  thf(d2_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.35/0.53       ( ![D:$i]:
% 0.35/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.35/0.53         (((X20) != (X22))
% 0.35/0.53          | (r2_hidden @ X20 @ X21)
% 0.35/0.53          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (![X19 : $i, X22 : $i]: (r2_hidden @ X22 @ (k2_tarski @ X22 @ X19))),
% 0.35/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.35/0.53  thf('41', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['38', '40'])).
% 0.35/0.53  thf('42', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.35/0.53      inference('clc', [status(thm)], ['35', '41'])).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      (![X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X23 @ X21)
% 0.35/0.53          | ((X23) = (X22))
% 0.35/0.53          | ((X23) = (X19))
% 0.35/0.53          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.35/0.53         (((X23) = (X19))
% 0.35/0.53          | ((X23) = (X22))
% 0.35/0.53          | ~ (r2_hidden @ X23 @ (k2_tarski @ X22 @ X19)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.35/0.53  thf('45', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_D_1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['42', '44'])).
% 0.35/0.53  thf('46', plain, (((sk_A) != (sk_D_1))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('47', plain, (((sk_A) != (sk_C))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('48', plain, ($false),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['45', '46', '47'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
