%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uy9PRxeIfb

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:46 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 234 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  482 (1562 expanded)
%              Number of equality atoms :   63 ( 188 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X27 @ X27 @ X28 @ X29 )
      = ( k1_enumset1 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X36: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X34 @ X35 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X34 ) @ ( k1_setfam_1 @ X35 ) ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X36: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) )
      | ( X32 != X33 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X33: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('34',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','40'])).

thf('42',plain,(
    ! [X33: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('43',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','40'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uy9PRxeIfb
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 449 iterations in 0.177s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(t70_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i]:
% 0.38/0.62         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.38/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.62  thf(t69_enumset1, axiom,
% 0.38/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.62  thf('1', plain, (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.38/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf(t46_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.38/0.62       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.62         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.38/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.38/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf(t71_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.62         ((k2_enumset1 @ X27 @ X27 @ X28 @ X29)
% 0.38/0.62           = (k1_enumset1 @ X27 @ X28 @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i]:
% 0.38/0.62         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.38/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.38/0.62           = (k2_tarski @ X1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['4', '7'])).
% 0.38/0.62  thf(t11_setfam_1, axiom,
% 0.38/0.62    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.38/0.62  thf('9', plain, (![X36 : $i]: ((k1_setfam_1 @ (k1_tarski @ X36)) = (X36))),
% 0.38/0.62      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.38/0.62  thf(t10_setfam_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.62          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.38/0.62            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X34 : $i, X35 : $i]:
% 0.38/0.62         (((X34) = (k1_xboole_0))
% 0.38/0.62          | ((k1_setfam_1 @ (k2_xboole_0 @ X34 @ X35))
% 0.38/0.62              = (k3_xboole_0 @ (k1_setfam_1 @ X34) @ (k1_setfam_1 @ X35)))
% 0.38/0.62          | ((X35) = (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.38/0.62            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.38/0.62          | ((X1) = (k1_xboole_0))
% 0.38/0.62          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.38/0.62            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.38/0.62          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.38/0.62          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['8', '11'])).
% 0.38/0.62  thf('13', plain, (![X36 : $i]: ((k1_setfam_1 @ (k1_tarski @ X36)) = (X36))),
% 0.38/0.62      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.38/0.62          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.38/0.62          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf(t12_setfam_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.38/0.62         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.38/0.62        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.38/0.62        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.62        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.62  thf(t16_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.38/0.62          ( ( A ) = ( B ) ) ) ))).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X32 : $i, X33 : $i]:
% 0.38/0.62         (~ (r1_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33))
% 0.38/0.62          | ((X32) != (X33)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X33 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X33))),
% 0.38/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.38/0.62        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['17', '19'])).
% 0.38/0.62  thf(t17_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.38/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.62  thf(t2_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.38/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.62  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf(d10_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X2 : $i, X4 : $i]:
% 0.38/0.62         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['21', '26'])).
% 0.38/0.62  thf(t47_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.38/0.62           = (k4_xboole_0 @ X8 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.38/0.62           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf(t48_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X10 : $i, X11 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.38/0.62           = (k3_xboole_0 @ X10 @ X11))),
% 0.38/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.38/0.62           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.38/0.62           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['21', '26'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['29', '34'])).
% 0.38/0.62  thf(t83_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (![X12 : $i, X14 : $i]:
% 0.38/0.62         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.62  thf('38', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.38/0.62  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf('41', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['20', '40'])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X33 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X33))),
% 0.38/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.62  thf('43', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.62  thf('44', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['20', '40'])).
% 0.38/0.62  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.62  thf('46', plain, ($false),
% 0.38/0.62      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
