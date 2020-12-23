%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.13OqMMk3ey

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:54 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 216 expanded)
%              Number of leaves         :   23 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  565 (1695 expanded)
%              Number of equality atoms :   75 ( 201 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('21',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ( X20 = X21 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ( X20 = X21 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( ( k4_xboole_0 @ X11 @ X10 )
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
       != ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1
      = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['13','41'])).

thf('43',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( ( k4_xboole_0 @ X11 @ X10 )
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
     != k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['47','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['47','53'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference(demod,[status(thm)],['45','58'])).

thf('60',plain,(
    sk_A = sk_C_1 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.13OqMMk3ey
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.98/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.98/1.17  % Solved by: fo/fo7.sh
% 0.98/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.17  % done 1795 iterations in 0.724s
% 0.98/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.98/1.17  % SZS output start Refutation
% 0.98/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.98/1.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.98/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.17  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.98/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.17  thf(sk_B_type, type, sk_B: $i > $i).
% 0.98/1.17  thf(t71_xboole_1, conjecture,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.98/1.17         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.98/1.17       ( ( A ) = ( C ) ) ))).
% 0.98/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.98/1.17        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.98/1.17            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.98/1.17          ( ( A ) = ( C ) ) ) )),
% 0.98/1.17    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.98/1.17  thf('0', plain,
% 0.98/1.17      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(commutativity_k2_xboole_0, axiom,
% 0.98/1.17    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.98/1.17  thf('1', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.98/1.17  thf(t3_boole, axiom,
% 0.98/1.17    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.98/1.17  thf('2', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.98/1.17      inference('cnf', [status(esa)], [t3_boole])).
% 0.98/1.17  thf(t48_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.98/1.17  thf('3', plain,
% 0.98/1.17      (![X18 : $i, X19 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.98/1.17           = (k3_xboole_0 @ X18 @ X19))),
% 0.98/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.98/1.17  thf('4', plain,
% 0.98/1.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.98/1.17      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.17  thf(t2_boole, axiom,
% 0.98/1.17    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.98/1.17  thf('5', plain,
% 0.98/1.17      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.98/1.17      inference('cnf', [status(esa)], [t2_boole])).
% 0.98/1.17  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.98/1.17      inference('demod', [status(thm)], ['4', '5'])).
% 0.98/1.17  thf(t41_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.98/1.17       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.98/1.17  thf('7', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.98/1.17           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.98/1.17  thf('8', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((k1_xboole_0)
% 0.98/1.17           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.98/1.17      inference('sup+', [status(thm)], ['6', '7'])).
% 0.98/1.17  thf(t39_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.98/1.17  thf('9', plain,
% 0.98/1.17      (![X12 : $i, X13 : $i]:
% 0.98/1.17         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.98/1.17           = (k2_xboole_0 @ X12 @ X13))),
% 0.98/1.17      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.98/1.17  thf('10', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.98/1.17      inference('demod', [status(thm)], ['8', '9'])).
% 0.98/1.17  thf('11', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.98/1.17      inference('sup+', [status(thm)], ['1', '10'])).
% 0.98/1.17  thf('12', plain,
% 0.98/1.17      (((k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)))),
% 0.98/1.17      inference('sup+', [status(thm)], ['0', '11'])).
% 0.98/1.17  thf('13', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.98/1.17  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(d1_xboole_0, axiom,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.98/1.17  thf('15', plain,
% 0.98/1.17      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.98/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.98/1.17  thf(t4_xboole_0, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.98/1.17            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.98/1.17       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.98/1.17            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.98/1.17  thf('16', plain,
% 0.98/1.17      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.98/1.17         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.98/1.17          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.98/1.17  thf('17', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['15', '16'])).
% 0.98/1.17  thf('18', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['14', '17'])).
% 0.98/1.17  thf('19', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('20', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['15', '16'])).
% 0.98/1.17  thf('21', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.98/1.17  thf(t8_boole, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.98/1.17  thf('22', plain,
% 0.98/1.17      (![X20 : $i, X21 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X20) | ~ (v1_xboole_0 @ X21) | ((X20) = (X21)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t8_boole])).
% 0.98/1.17  thf('23', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (((k3_xboole_0 @ sk_A @ sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['21', '22'])).
% 0.98/1.17  thf('24', plain,
% 0.98/1.17      (((k3_xboole_0 @ sk_A @ sk_B_1) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['18', '23'])).
% 0.98/1.17  thf('25', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.98/1.17  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.98/1.17  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.17  thf('27', plain,
% 0.98/1.17      (![X20 : $i, X21 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X20) | ~ (v1_xboole_0 @ X21) | ((X20) = (X21)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t8_boole])).
% 0.98/1.17  thf('28', plain,
% 0.98/1.17      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['26', '27'])).
% 0.98/1.17  thf('29', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['25', '28'])).
% 0.98/1.17  thf('30', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.98/1.17      inference('demod', [status(thm)], ['24', '29'])).
% 0.98/1.17  thf('31', plain,
% 0.98/1.17      (![X18 : $i, X19 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.98/1.17           = (k3_xboole_0 @ X18 @ X19))),
% 0.98/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.98/1.17  thf('32', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.98/1.17           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.98/1.17  thf(t32_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.98/1.17       ( ( A ) = ( B ) ) ))).
% 0.98/1.17  thf('33', plain,
% 0.98/1.17      (![X10 : $i, X11 : $i]:
% 0.98/1.17         (((X11) = (X10))
% 0.98/1.17          | ((k4_xboole_0 @ X11 @ X10) != (k4_xboole_0 @ X10 @ X11)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.98/1.17  thf('34', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         (((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 0.98/1.17            != (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.98/1.17          | ((X0) = (k4_xboole_0 @ X2 @ X1)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['32', '33'])).
% 0.98/1.18  thf('35', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (((k3_xboole_0 @ X1 @ X0)
% 0.98/1.18            != (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))
% 0.98/1.18          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['31', '34'])).
% 0.98/1.18  thf('36', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.98/1.18      inference('demod', [status(thm)], ['8', '9'])).
% 0.98/1.18  thf('37', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.98/1.18          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 0.98/1.18      inference('demod', [status(thm)], ['35', '36'])).
% 0.98/1.18  thf('38', plain,
% 0.98/1.18      ((((k1_xboole_0) != (k1_xboole_0))
% 0.98/1.18        | ((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['30', '37'])).
% 0.98/1.18  thf('39', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.98/1.18      inference('simplify', [status(thm)], ['38'])).
% 0.98/1.18  thf('40', plain,
% 0.98/1.18      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.98/1.18           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.98/1.18      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.98/1.18  thf('41', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ sk_C_1 @ X0)
% 0.98/1.18           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['39', '40'])).
% 0.98/1.18  thf('42', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ sk_C_1 @ X0)
% 0.98/1.18           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['13', '41'])).
% 0.98/1.18  thf('43', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.98/1.18      inference('demod', [status(thm)], ['12', '42'])).
% 0.98/1.18  thf('44', plain,
% 0.98/1.18      (![X10 : $i, X11 : $i]:
% 0.98/1.18         (((X11) = (X10))
% 0.98/1.18          | ((k4_xboole_0 @ X11 @ X10) != (k4_xboole_0 @ X10 @ X11)))),
% 0.98/1.18      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.98/1.18  thf('45', plain,
% 0.98/1.18      ((((k4_xboole_0 @ sk_A @ sk_C_1) != (k1_xboole_0)) | ((sk_A) = (sk_C_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['43', '44'])).
% 0.98/1.18  thf('46', plain,
% 0.98/1.18      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('47', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.98/1.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.98/1.18  thf('48', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['25', '28'])).
% 0.98/1.18  thf('49', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.98/1.18          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 0.98/1.18      inference('demod', [status(thm)], ['35', '36'])).
% 0.98/1.18  thf('50', plain,
% 0.98/1.18      ((((k1_xboole_0) != (k1_xboole_0))
% 0.98/1.18        | ((sk_A) = (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['48', '49'])).
% 0.98/1.18  thf('51', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.98/1.18      inference('simplify', [status(thm)], ['50'])).
% 0.98/1.18  thf('52', plain,
% 0.98/1.18      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.98/1.18           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.98/1.18      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.98/1.18  thf('53', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ sk_A @ X0)
% 0.98/1.18           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['51', '52'])).
% 0.98/1.18  thf('54', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ sk_A @ X0)
% 0.98/1.18           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['47', '53'])).
% 0.98/1.18  thf('55', plain,
% 0.98/1.18      (((k4_xboole_0 @ sk_A @ sk_C_1)
% 0.98/1.18         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B_1)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['46', '54'])).
% 0.98/1.18  thf('56', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((k4_xboole_0 @ sk_A @ X0)
% 0.98/1.18           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['47', '53'])).
% 0.98/1.18  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.98/1.18      inference('demod', [status(thm)], ['4', '5'])).
% 0.98/1.18  thf('58', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.98/1.18      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.98/1.18  thf('59', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (sk_C_1)))),
% 0.98/1.18      inference('demod', [status(thm)], ['45', '58'])).
% 0.98/1.18  thf('60', plain, (((sk_A) = (sk_C_1))),
% 0.98/1.18      inference('simplify', [status(thm)], ['59'])).
% 0.98/1.18  thf('61', plain, (((sk_A) != (sk_C_1))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('62', plain, ($false),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.98/1.18  
% 0.98/1.18  % SZS output end Refutation
% 0.98/1.18  
% 0.98/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
