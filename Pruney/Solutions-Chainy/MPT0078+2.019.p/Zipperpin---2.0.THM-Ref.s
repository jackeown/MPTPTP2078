%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGUdc2zkT9

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:55 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 147 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  566 (1085 expanded)
%              Number of equality atoms :   71 ( 134 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['8','11'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17','22'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,(
    r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','54'])).

thf('56',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_C_1 = sk_A ),
    inference(demod,[status(thm)],['25','26','27','60'])).

thf('62',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGUdc2zkT9
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.40/2.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.40/2.67  % Solved by: fo/fo7.sh
% 2.40/2.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.40/2.67  % done 1774 iterations in 2.203s
% 2.40/2.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.40/2.67  % SZS output start Refutation
% 2.40/2.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.40/2.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.40/2.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.40/2.67  thf(sk_B_type, type, sk_B: $i > $i).
% 2.40/2.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.40/2.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.40/2.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.40/2.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.40/2.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.40/2.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.40/2.67  thf(sk_A_type, type, sk_A: $i).
% 2.40/2.67  thf(t71_xboole_1, conjecture,
% 2.40/2.67    (![A:$i,B:$i,C:$i]:
% 2.40/2.67     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 2.40/2.67         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.40/2.67       ( ( A ) = ( C ) ) ))).
% 2.40/2.67  thf(zf_stmt_0, negated_conjecture,
% 2.40/2.67    (~( ![A:$i,B:$i,C:$i]:
% 2.40/2.67        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 2.40/2.67            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.40/2.67          ( ( A ) = ( C ) ) ) )),
% 2.40/2.67    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 2.40/2.67  thf('0', plain,
% 2.40/2.67      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 2.40/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.67  thf(commutativity_k2_xboole_0, axiom,
% 2.40/2.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.40/2.67  thf('1', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.40/2.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.40/2.67  thf('2', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 2.40/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.67  thf(t7_xboole_0, axiom,
% 2.40/2.67    (![A:$i]:
% 2.40/2.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.40/2.67          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.40/2.67  thf('3', plain,
% 2.40/2.67      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.40/2.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.40/2.67  thf(t4_xboole_0, axiom,
% 2.40/2.67    (![A:$i,B:$i]:
% 2.40/2.67     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.40/2.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.40/2.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.40/2.67            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.40/2.67  thf('4', plain,
% 2.40/2.67      (![X2 : $i, X4 : $i, X5 : $i]:
% 2.40/2.67         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 2.40/2.67          | ~ (r1_xboole_0 @ X2 @ X5))),
% 2.40/2.67      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.40/2.67  thf('5', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]:
% 2.40/2.67         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.40/2.67      inference('sup-', [status(thm)], ['3', '4'])).
% 2.40/2.67  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 2.40/2.67      inference('sup-', [status(thm)], ['2', '5'])).
% 2.40/2.67  thf(t51_xboole_1, axiom,
% 2.40/2.67    (![A:$i,B:$i]:
% 2.40/2.67     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.40/2.67       ( A ) ))).
% 2.40/2.67  thf('7', plain,
% 2.40/2.67      (![X22 : $i, X23 : $i]:
% 2.40/2.67         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 2.40/2.67           = (X22))),
% 2.40/2.67      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.40/2.67  thf('8', plain,
% 2.40/2.67      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 2.40/2.67      inference('sup+', [status(thm)], ['6', '7'])).
% 2.40/2.67  thf('9', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.40/2.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.40/2.67  thf(t1_boole, axiom,
% 2.40/2.67    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.40/2.67  thf('10', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.40/2.67      inference('cnf', [status(esa)], [t1_boole])).
% 2.40/2.67  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.40/2.67      inference('sup+', [status(thm)], ['9', '10'])).
% 2.40/2.67  thf('12', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 2.40/2.67      inference('demod', [status(thm)], ['8', '11'])).
% 2.40/2.67  thf(t41_xboole_1, axiom,
% 2.40/2.67    (![A:$i,B:$i,C:$i]:
% 2.40/2.67     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.40/2.67       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.40/2.67  thf('13', plain,
% 2.40/2.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 2.40/2.67           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 2.40/2.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.40/2.67  thf('14', plain,
% 2.40/2.67      (![X0 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ sk_A @ X0)
% 2.40/2.67           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 2.40/2.67      inference('sup+', [status(thm)], ['12', '13'])).
% 2.40/2.67  thf('15', plain,
% 2.40/2.67      (![X0 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ sk_A @ X0)
% 2.40/2.67           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 2.40/2.67      inference('sup+', [status(thm)], ['1', '14'])).
% 2.40/2.67  thf('16', plain,
% 2.40/2.67      (((k4_xboole_0 @ sk_A @ sk_C_1)
% 2.40/2.67         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B_1)))),
% 2.40/2.67      inference('sup+', [status(thm)], ['0', '15'])).
% 2.40/2.67  thf('17', plain,
% 2.40/2.67      (![X0 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ sk_A @ X0)
% 2.40/2.67           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 2.40/2.67      inference('sup+', [status(thm)], ['1', '14'])).
% 2.40/2.67  thf(t3_boole, axiom,
% 2.40/2.67    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.40/2.67  thf('18', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 2.40/2.67      inference('cnf', [status(esa)], [t3_boole])).
% 2.40/2.67  thf(t48_xboole_1, axiom,
% 2.40/2.67    (![A:$i,B:$i]:
% 2.40/2.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.40/2.67  thf('19', plain,
% 2.40/2.67      (![X20 : $i, X21 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 2.40/2.67           = (k3_xboole_0 @ X20 @ X21))),
% 2.40/2.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.40/2.67  thf('20', plain,
% 2.40/2.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.40/2.67      inference('sup+', [status(thm)], ['18', '19'])).
% 2.40/2.67  thf(t2_boole, axiom,
% 2.40/2.67    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.40/2.67  thf('21', plain,
% 2.40/2.67      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.40/2.67      inference('cnf', [status(esa)], [t2_boole])).
% 2.40/2.67  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.40/2.67      inference('demod', [status(thm)], ['20', '21'])).
% 2.40/2.67  thf('23', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 2.40/2.67      inference('demod', [status(thm)], ['16', '17', '22'])).
% 2.40/2.67  thf(t39_xboole_1, axiom,
% 2.40/2.67    (![A:$i,B:$i]:
% 2.40/2.67     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.40/2.67  thf('24', plain,
% 2.40/2.67      (![X14 : $i, X15 : $i]:
% 2.40/2.67         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 2.40/2.67           = (k2_xboole_0 @ X14 @ X15))),
% 2.40/2.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.40/2.67  thf('25', plain,
% 2.40/2.67      (((k2_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 2.40/2.67      inference('sup+', [status(thm)], ['23', '24'])).
% 2.40/2.67  thf('26', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.40/2.67      inference('cnf', [status(esa)], [t1_boole])).
% 2.40/2.67  thf('27', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.40/2.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.40/2.67  thf('28', plain,
% 2.40/2.67      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 2.40/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.67  thf('29', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.40/2.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.40/2.67  thf('30', plain,
% 2.40/2.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 2.40/2.67           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 2.40/2.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.40/2.67  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.40/2.67      inference('demod', [status(thm)], ['20', '21'])).
% 2.40/2.67  thf('32', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 2.40/2.67           = (k1_xboole_0))),
% 2.40/2.67      inference('sup+', [status(thm)], ['30', '31'])).
% 2.40/2.67  thf('33', plain,
% 2.40/2.67      (![X14 : $i, X15 : $i]:
% 2.40/2.67         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 2.40/2.67           = (k2_xboole_0 @ X14 @ X15))),
% 2.40/2.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.40/2.67  thf('34', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 2.40/2.67      inference('demod', [status(thm)], ['32', '33'])).
% 2.40/2.67  thf(l32_xboole_1, axiom,
% 2.40/2.67    (![A:$i,B:$i]:
% 2.40/2.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.40/2.67  thf('35', plain,
% 2.40/2.67      (![X7 : $i, X8 : $i]:
% 2.40/2.67         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 2.40/2.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.40/2.67  thf('36', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]:
% 2.40/2.67         (((k1_xboole_0) != (k1_xboole_0))
% 2.40/2.67          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.40/2.67      inference('sup-', [status(thm)], ['34', '35'])).
% 2.40/2.67  thf('37', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.40/2.67      inference('simplify', [status(thm)], ['36'])).
% 2.40/2.67  thf('38', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 2.40/2.67      inference('sup+', [status(thm)], ['29', '37'])).
% 2.40/2.67  thf('39', plain, ((r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1))),
% 2.40/2.67      inference('sup+', [status(thm)], ['28', '38'])).
% 2.40/2.67  thf('40', plain,
% 2.40/2.67      (![X7 : $i, X9 : $i]:
% 2.40/2.67         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 2.40/2.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.40/2.67  thf('41', plain,
% 2.40/2.67      (((k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 2.40/2.67      inference('sup-', [status(thm)], ['39', '40'])).
% 2.40/2.67  thf('42', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.40/2.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.40/2.67  thf('43', plain,
% 2.40/2.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.40/2.67         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 2.40/2.67           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 2.40/2.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.40/2.67  thf('44', plain,
% 2.40/2.67      (![X7 : $i, X8 : $i]:
% 2.40/2.67         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 2.40/2.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.40/2.67  thf('45', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.67         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 2.40/2.67          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.40/2.67      inference('sup-', [status(thm)], ['43', '44'])).
% 2.40/2.67  thf('46', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.67         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 2.40/2.67          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 2.40/2.67      inference('sup-', [status(thm)], ['42', '45'])).
% 2.40/2.67  thf('47', plain,
% 2.40/2.67      ((((k1_xboole_0) != (k1_xboole_0))
% 2.40/2.67        | (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_A))),
% 2.40/2.67      inference('sup-', [status(thm)], ['41', '46'])).
% 2.40/2.67  thf('48', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 2.40/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.67  thf('49', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]:
% 2.40/2.67         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.40/2.67      inference('sup-', [status(thm)], ['3', '4'])).
% 2.40/2.67  thf('50', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 2.40/2.67      inference('sup-', [status(thm)], ['48', '49'])).
% 2.40/2.67  thf('51', plain,
% 2.40/2.67      (![X22 : $i, X23 : $i]:
% 2.40/2.67         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 2.40/2.67           = (X22))),
% 2.40/2.67      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.40/2.67  thf('52', plain,
% 2.40/2.67      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1))
% 2.40/2.67         = (sk_C_1))),
% 2.40/2.67      inference('sup+', [status(thm)], ['50', '51'])).
% 2.40/2.67  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.40/2.67      inference('sup+', [status(thm)], ['9', '10'])).
% 2.40/2.67  thf('54', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 2.40/2.67      inference('demod', [status(thm)], ['52', '53'])).
% 2.40/2.67  thf('55', plain,
% 2.40/2.67      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_C_1 @ sk_A))),
% 2.40/2.67      inference('demod', [status(thm)], ['47', '54'])).
% 2.40/2.67  thf('56', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.40/2.67      inference('simplify', [status(thm)], ['55'])).
% 2.40/2.67  thf(t12_xboole_1, axiom,
% 2.40/2.67    (![A:$i,B:$i]:
% 2.40/2.67     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.40/2.67  thf('57', plain,
% 2.40/2.67      (![X10 : $i, X11 : $i]:
% 2.40/2.67         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 2.40/2.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.40/2.67  thf('58', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 2.40/2.67      inference('sup-', [status(thm)], ['56', '57'])).
% 2.40/2.67  thf('59', plain,
% 2.40/2.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.40/2.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.40/2.67  thf('60', plain, (((k2_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 2.40/2.67      inference('demod', [status(thm)], ['58', '59'])).
% 2.40/2.67  thf('61', plain, (((sk_C_1) = (sk_A))),
% 2.40/2.67      inference('demod', [status(thm)], ['25', '26', '27', '60'])).
% 2.40/2.67  thf('62', plain, (((sk_A) != (sk_C_1))),
% 2.40/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.67  thf('63', plain, ($false),
% 2.40/2.67      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 2.40/2.67  
% 2.40/2.67  % SZS output end Refutation
% 2.40/2.67  
% 2.51/2.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
