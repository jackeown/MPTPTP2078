%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2EOPs4XRPL

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:05 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 158 expanded)
%              Number of leaves         :   31 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  559 (1084 expanded)
%              Number of equality atoms :   51 ( 108 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X42 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( r2_hidden @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['11','25'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_tarski @ X29 @ X28 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X40 @ X41 ) )
      = ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X40 @ X41 ) )
      = ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','46'])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('50',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('59',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2EOPs4XRPL
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.78  % Solved by: fo/fo7.sh
% 0.58/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.78  % done 818 iterations in 0.326s
% 0.58/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.78  % SZS output start Refutation
% 0.58/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.78  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(t46_zfmisc_1, conjecture,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( r2_hidden @ A @ B ) =>
% 0.58/0.78       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.58/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.78    (~( ![A:$i,B:$i]:
% 0.58/0.78        ( ( r2_hidden @ A @ B ) =>
% 0.58/0.78          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.58/0.78    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.58/0.78  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(t38_zfmisc_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.58/0.78       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.58/0.78  thf('2', plain,
% 0.58/0.78      (![X42 : $i, X44 : $i, X45 : $i]:
% 0.58/0.78         ((r1_tarski @ (k2_tarski @ X42 @ X44) @ X45)
% 0.58/0.78          | ~ (r2_hidden @ X44 @ X45)
% 0.58/0.78          | ~ (r2_hidden @ X42 @ X45))),
% 0.58/0.78      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.58/0.78  thf('3', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.58/0.78          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.78  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)),
% 0.58/0.78      inference('sup-', [status(thm)], ['0', '3'])).
% 0.58/0.78  thf(t69_enumset1, axiom,
% 0.58/0.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.78  thf('5', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.58/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.78  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.58/0.78      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.78  thf(t28_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.78  thf('7', plain,
% 0.58/0.78      (![X19 : $i, X20 : $i]:
% 0.58/0.78         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.58/0.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.78  thf('8', plain,
% 0.58/0.78      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.78  thf(t100_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.78  thf('9', plain,
% 0.58/0.78      (![X16 : $i, X17 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X16 @ X17)
% 0.58/0.78           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.78  thf('10', plain,
% 0.58/0.78      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.58/0.78         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.78  thf(t3_xboole_0, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.58/0.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.78            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.58/0.78  thf('11', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]:
% 0.58/0.78         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.78  thf(d10_xboole_0, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.78  thf('12', plain,
% 0.58/0.78      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.58/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.78  thf('13', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.58/0.78      inference('simplify', [status(thm)], ['12'])).
% 0.58/0.78  thf('14', plain,
% 0.58/0.78      (![X19 : $i, X20 : $i]:
% 0.58/0.78         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.58/0.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.78  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.78  thf('16', plain,
% 0.58/0.78      (![X16 : $i, X17 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X16 @ X17)
% 0.58/0.78           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.78  thf('17', plain,
% 0.58/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['15', '16'])).
% 0.58/0.78  thf(d5_xboole_0, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.58/0.78       ( ![D:$i]:
% 0.58/0.78         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.78           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.58/0.78  thf('18', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X7 @ X6)
% 0.58/0.78          | (r2_hidden @ X7 @ X4)
% 0.58/0.78          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.58/0.78      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.78  thf('19', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.58/0.78         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['18'])).
% 0.58/0.78  thf('20', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['17', '19'])).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['15', '16'])).
% 0.58/0.78  thf('22', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X7 @ X6)
% 0.58/0.78          | ~ (r2_hidden @ X7 @ X5)
% 0.58/0.78          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.58/0.78      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.78  thf('23', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X7 @ X5)
% 0.58/0.78          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.78  thf('24', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.58/0.78          | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['21', '23'])).
% 0.58/0.78  thf('25', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('clc', [status(thm)], ['20', '24'])).
% 0.58/0.78  thf('26', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.58/0.78      inference('sup-', [status(thm)], ['11', '25'])).
% 0.58/0.78  thf(t83_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.78  thf('27', plain,
% 0.58/0.78      (![X23 : $i, X24 : $i]:
% 0.58/0.78         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 0.58/0.78      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 0.58/0.78           = (k5_xboole_0 @ X1 @ X1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.78  thf('29', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.58/0.78         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 0.58/0.78          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.58/0.78          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.78  thf(d1_xboole_0, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.78  thf('30', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.78  thf('31', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.58/0.78          | ((X2) = (k4_xboole_0 @ X0 @ X1))
% 0.58/0.78          | ~ (v1_xboole_0 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.78  thf(t39_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.78  thf('32', plain,
% 0.58/0.78      (![X21 : $i, X22 : $i]:
% 0.58/0.78         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 0.58/0.78           = (k2_xboole_0 @ X21 @ X22))),
% 0.58/0.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.78  thf(commutativity_k2_tarski, axiom,
% 0.58/0.78    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.58/0.78  thf('33', plain,
% 0.58/0.78      (![X28 : $i, X29 : $i]:
% 0.58/0.78         ((k2_tarski @ X29 @ X28) = (k2_tarski @ X28 @ X29))),
% 0.58/0.78      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.58/0.78  thf(l51_zfmisc_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.78  thf('34', plain,
% 0.58/0.78      (![X40 : $i, X41 : $i]:
% 0.58/0.78         ((k3_tarski @ (k2_tarski @ X40 @ X41)) = (k2_xboole_0 @ X40 @ X41))),
% 0.58/0.78      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.78  thf('35', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.78      inference('sup+', [status(thm)], ['33', '34'])).
% 0.58/0.78  thf('36', plain,
% 0.58/0.78      (![X40 : $i, X41 : $i]:
% 0.58/0.78         ((k3_tarski @ (k2_tarski @ X40 @ X41)) = (k2_xboole_0 @ X40 @ X41))),
% 0.58/0.78      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.78  thf('37', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.78      inference('sup+', [status(thm)], ['35', '36'])).
% 0.58/0.78  thf(t1_boole, axiom,
% 0.58/0.78    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.78  thf('38', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [t1_boole])).
% 0.58/0.78  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['37', '38'])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['32', '39'])).
% 0.58/0.78  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['37', '38'])).
% 0.58/0.78  thf('42', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('demod', [status(thm)], ['40', '41'])).
% 0.58/0.78  thf('43', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X7 @ X5)
% 0.58/0.78          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.78  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.58/0.78      inference('condensation', [status(thm)], ['44'])).
% 0.58/0.78  thf('46', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['31', '45'])).
% 0.58/0.78  thf('47', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))
% 0.58/0.78          | ~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['28', '46'])).
% 0.58/0.78  thf('48', plain,
% 0.58/0.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.78  thf('49', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('clc', [status(thm)], ['20', '24'])).
% 0.58/0.78  thf('50', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('51', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('demod', [status(thm)], ['47', '50'])).
% 0.58/0.78  thf('52', plain,
% 0.58/0.78      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.58/0.78      inference('demod', [status(thm)], ['10', '51'])).
% 0.58/0.78  thf('53', plain,
% 0.58/0.78      (![X21 : $i, X22 : $i]:
% 0.58/0.78         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 0.58/0.78           = (k2_xboole_0 @ X21 @ X22))),
% 0.58/0.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.78  thf('54', plain,
% 0.58/0.78      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.58/0.78         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['52', '53'])).
% 0.58/0.78  thf('55', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [t1_boole])).
% 0.58/0.78  thf('56', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['54', '55'])).
% 0.58/0.78  thf('57', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('58', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.78      inference('sup+', [status(thm)], ['35', '36'])).
% 0.58/0.78  thf('59', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.58/0.78      inference('demod', [status(thm)], ['57', '58'])).
% 0.58/0.78  thf('60', plain, ($false),
% 0.58/0.78      inference('simplify_reflect-', [status(thm)], ['56', '59'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
