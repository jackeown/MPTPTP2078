%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j64CdHLrCH

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 177 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  506 (1240 expanded)
%              Number of equality atoms :   49 ( 112 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,
    ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf('53',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('59',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j64CdHLrCH
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:05:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 88 iterations in 0.046s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(t63_xboole_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.51       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.51          ( r1_xboole_0 @ A @ C ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.22/0.51  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t7_xboole_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.51  thf(t4_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.22/0.51          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.51  thf('6', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(l32_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X7 : $i, X9 : $i]:
% 0.22/0.51         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.51  thf('8', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf(t48_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.22/0.51           = (k3_xboole_0 @ X18 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf(t3_boole, axiom,
% 0.22/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.51  thf('11', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.51  thf('12', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf(t16_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.51       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.22/0.51           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k3_xboole_0 @ sk_A @ X0)
% 0.22/0.51           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (((k3_xboole_0 @ sk_A @ sk_C_1) = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['5', '14'])).
% 0.22/0.51  thf(t2_boole, axiom,
% 0.22/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.51  thf('17', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X2 @ X3)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('19', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.22/0.51           = (k3_xboole_0 @ X18 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.51  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.22/0.51           = (k3_xboole_0 @ X18 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.51  thf('26', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.51  thf('27', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.22/0.51          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.51          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      ((~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ k1_xboole_0)
% 0.22/0.51        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '30'])).
% 0.22/0.51  thf('32', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.22/0.51           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.51           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.51  thf(t51_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.51       ( A ) ))).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.22/0.51           = (X20))),
% 0.22/0.51      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.22/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21))
% 0.22/0.51           = (X20))),
% 0.22/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ 
% 0.22/0.51           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.22/0.51           (k3_xboole_0 @ k1_xboole_0 @ X0)) = (X1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['35', '38'])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.51  thf(t39_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.22/0.51           = (k2_xboole_0 @ X15 @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ X1) = (X1))),
% 0.22/0.51      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.22/0.51  thf(t1_boole, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.51  thf('43', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.51          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '29'])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.22/0.51          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.51          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X2 @ X3)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.51          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf('52', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.51  thf('53', plain,
% 0.22/0.51      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.22/0.51          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.51  thf('55', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.51  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['51', '56'])).
% 0.22/0.51  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.51      inference('demod', [status(thm)], ['48', '57'])).
% 0.22/0.51  thf('59', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.22/0.51      inference('demod', [status(thm)], ['31', '32', '58'])).
% 0.22/0.51  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
