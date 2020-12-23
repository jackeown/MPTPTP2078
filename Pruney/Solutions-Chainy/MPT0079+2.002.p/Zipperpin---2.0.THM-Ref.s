%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAGmeqtUHo

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:56 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 622 expanded)
%              Number of leaves         :   23 ( 207 expanded)
%              Depth                    :   24
%              Number of atoms          : 1098 (4970 expanded)
%              Number of equality atoms :  134 ( 585 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('40',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['30','56'])).

thf('58',plain,(
    r1_tarski @ sk_A @ sk_D ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('63',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('70',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('83',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('88',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_D ) @ sk_B )
    = sk_D ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['85','90'])).

thf('92',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['60','91'])).

thf('93',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','92'])).

thf('94',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('95',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('96',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['85','90'])).

thf('97',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('98',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_A ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('105',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_D @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['95','106'])).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('109',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('111',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_D ) )
    = sk_C ),
    inference('sup+',[status(thm)],['109','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('120',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['94','122'])).

thf('124',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['60','91'])).

thf('125',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('126',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['93','126'])).

thf('128',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAGmeqtUHo
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:25:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.02/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.22  % Solved by: fo/fo7.sh
% 1.02/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.22  % done 2194 iterations in 0.766s
% 1.02/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.22  % SZS output start Refutation
% 1.02/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.22  thf(sk_D_type, type, sk_D: $i).
% 1.02/1.22  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.02/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(sk_C_type, type, sk_C: $i).
% 1.02/1.22  thf(t72_xboole_1, conjecture,
% 1.02/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.22     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.02/1.22         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.02/1.22       ( ( C ) = ( B ) ) ))).
% 1.02/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.22    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.22        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.02/1.22            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.02/1.22          ( ( C ) = ( B ) ) ) )),
% 1.02/1.22    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 1.02/1.22  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf(d7_xboole_0, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.02/1.22       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.02/1.22  thf('1', plain,
% 1.02/1.22      (![X4 : $i, X5 : $i]:
% 1.02/1.22         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.02/1.22      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.02/1.22  thf('2', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.02/1.22  thf(commutativity_k3_xboole_0, axiom,
% 1.02/1.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.02/1.22  thf('3', plain,
% 1.02/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.22  thf('4', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 1.02/1.22      inference('demod', [status(thm)], ['2', '3'])).
% 1.02/1.22  thf(t48_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.02/1.22  thf('5', plain,
% 1.02/1.22      (![X24 : $i, X25 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.02/1.22           = (k3_xboole_0 @ X24 @ X25))),
% 1.02/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.22  thf(l32_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.22  thf('6', plain,
% 1.02/1.22      (![X7 : $i, X8 : $i]:
% 1.02/1.22         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 1.02/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.22  thf('7', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 1.02/1.22          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['5', '6'])).
% 1.02/1.22  thf('8', plain,
% 1.02/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.02/1.22        | (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_D)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['4', '7'])).
% 1.02/1.22  thf('9', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_D))),
% 1.02/1.22      inference('simplify', [status(thm)], ['8'])).
% 1.02/1.22  thf(t12_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.02/1.22  thf('10', plain,
% 1.02/1.22      (![X10 : $i, X11 : $i]:
% 1.02/1.22         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 1.02/1.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.22  thf('11', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_D))
% 1.02/1.22         = (k4_xboole_0 @ sk_B @ sk_D))),
% 1.02/1.22      inference('sup-', [status(thm)], ['9', '10'])).
% 1.02/1.22  thf(t36_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.02/1.22  thf('12', plain,
% 1.02/1.22      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.02/1.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.02/1.22  thf('13', plain,
% 1.02/1.22      (![X10 : $i, X11 : $i]:
% 1.02/1.22         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 1.02/1.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.22  thf('14', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.02/1.22  thf(commutativity_k2_xboole_0, axiom,
% 1.02/1.22    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.02/1.22  thf('15', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.22  thf('16', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.02/1.22      inference('demod', [status(thm)], ['14', '15'])).
% 1.02/1.22  thf('17', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 1.02/1.22      inference('demod', [status(thm)], ['11', '16'])).
% 1.02/1.22  thf('18', plain,
% 1.02/1.22      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.02/1.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.02/1.22  thf('19', plain,
% 1.02/1.22      (![X7 : $i, X9 : $i]:
% 1.02/1.22         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 1.02/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.22  thf('20', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['18', '19'])).
% 1.02/1.22  thf(t41_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i]:
% 1.02/1.22     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.02/1.22       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.02/1.22  thf('21', plain,
% 1.02/1.22      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 1.02/1.22           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 1.02/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.22  thf('22', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.02/1.22      inference('demod', [status(thm)], ['20', '21'])).
% 1.02/1.22  thf('23', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('24', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.22  thf('25', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.02/1.22      inference('demod', [status(thm)], ['23', '24'])).
% 1.02/1.22  thf('26', plain,
% 1.02/1.22      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 1.02/1.22           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 1.02/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.22  thf('27', plain,
% 1.02/1.22      (![X7 : $i, X8 : $i]:
% 1.02/1.22         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 1.02/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.22  thf('28', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.02/1.22          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['26', '27'])).
% 1.02/1.22  thf('29', plain,
% 1.02/1.22      (![X0 : $i]:
% 1.02/1.22         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)) != (k1_xboole_0))
% 1.02/1.22          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 1.02/1.22      inference('sup-', [status(thm)], ['25', '28'])).
% 1.02/1.22  thf('30', plain,
% 1.02/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.02/1.22        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D))),
% 1.02/1.22      inference('sup-', [status(thm)], ['22', '29'])).
% 1.02/1.22  thf('31', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('32', plain,
% 1.02/1.22      (![X4 : $i, X5 : $i]:
% 1.02/1.22         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.02/1.22      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.02/1.22  thf('33', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['31', '32'])).
% 1.02/1.22  thf('34', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 1.02/1.22          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['5', '6'])).
% 1.02/1.22  thf('35', plain,
% 1.02/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.02/1.22        | (r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['33', '34'])).
% 1.02/1.22  thf('36', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))),
% 1.02/1.22      inference('simplify', [status(thm)], ['35'])).
% 1.02/1.22  thf('37', plain,
% 1.02/1.22      (![X10 : $i, X11 : $i]:
% 1.02/1.22         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 1.02/1.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.22  thf('38', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 1.02/1.22         = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.02/1.22      inference('sup-', [status(thm)], ['36', '37'])).
% 1.02/1.22  thf('39', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.02/1.22      inference('demod', [status(thm)], ['14', '15'])).
% 1.02/1.22  thf('40', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['38', '39'])).
% 1.02/1.22  thf(t40_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.02/1.22  thf('41', plain,
% 1.02/1.22      (![X19 : $i, X20 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 1.02/1.22           = (k4_xboole_0 @ X19 @ X20))),
% 1.02/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.02/1.22  thf('42', plain,
% 1.02/1.22      (![X24 : $i, X25 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.02/1.22           = (k3_xboole_0 @ X24 @ X25))),
% 1.02/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.22  thf('43', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.02/1.22           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.02/1.22      inference('sup+', [status(thm)], ['41', '42'])).
% 1.02/1.22  thf('44', plain,
% 1.02/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.22  thf('45', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.02/1.22           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('demod', [status(thm)], ['43', '44'])).
% 1.02/1.22  thf('46', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.02/1.22      inference('demod', [status(thm)], ['20', '21'])).
% 1.02/1.22  thf('47', plain,
% 1.02/1.22      (![X24 : $i, X25 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.02/1.22           = (k3_xboole_0 @ X24 @ X25))),
% 1.02/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.22  thf('48', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.02/1.22           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('sup+', [status(thm)], ['46', '47'])).
% 1.02/1.22  thf(t3_boole, axiom,
% 1.02/1.22    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.22  thf('49', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.02/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.02/1.22  thf('50', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('demod', [status(thm)], ['48', '49'])).
% 1.02/1.22  thf('51', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.02/1.22           = (X0))),
% 1.02/1.22      inference('demod', [status(thm)], ['45', '50'])).
% 1.02/1.22  thf('52', plain,
% 1.02/1.22      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_C) = (sk_A))),
% 1.02/1.22      inference('sup+', [status(thm)], ['40', '51'])).
% 1.02/1.22  thf('53', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.22  thf('54', plain,
% 1.02/1.22      (![X19 : $i, X20 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 1.02/1.22           = (k4_xboole_0 @ X19 @ X20))),
% 1.02/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.02/1.22  thf('55', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.02/1.22           = (k4_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('sup+', [status(thm)], ['53', '54'])).
% 1.02/1.22  thf('56', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['52', '55'])).
% 1.02/1.22  thf('57', plain,
% 1.02/1.22      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_D))),
% 1.02/1.22      inference('demod', [status(thm)], ['30', '56'])).
% 1.02/1.22  thf('58', plain, ((r1_tarski @ sk_A @ sk_D)),
% 1.02/1.22      inference('simplify', [status(thm)], ['57'])).
% 1.02/1.22  thf('59', plain,
% 1.02/1.22      (![X10 : $i, X11 : $i]:
% 1.02/1.22         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 1.02/1.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.22  thf('60', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_D))),
% 1.02/1.22      inference('sup-', [status(thm)], ['58', '59'])).
% 1.02/1.22  thf('61', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.02/1.22      inference('demod', [status(thm)], ['23', '24'])).
% 1.02/1.22  thf('62', plain,
% 1.02/1.22      (![X19 : $i, X20 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 1.02/1.22           = (k4_xboole_0 @ X19 @ X20))),
% 1.02/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.02/1.22  thf('63', plain,
% 1.02/1.22      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 1.02/1.22         = (k4_xboole_0 @ sk_C @ sk_D))),
% 1.02/1.22      inference('sup+', [status(thm)], ['61', '62'])).
% 1.02/1.22  thf(t39_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.02/1.22  thf('64', plain,
% 1.02/1.22      (![X16 : $i, X17 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 1.02/1.22           = (k2_xboole_0 @ X16 @ X17))),
% 1.02/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.02/1.22  thf('65', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C @ sk_D))
% 1.02/1.22         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.02/1.22      inference('sup+', [status(thm)], ['63', '64'])).
% 1.02/1.22  thf('66', plain,
% 1.02/1.22      (![X16 : $i, X17 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 1.02/1.22           = (k2_xboole_0 @ X16 @ X17))),
% 1.02/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.02/1.22  thf('67', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.22  thf('68', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_C @ sk_D)
% 1.02/1.22         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.02/1.22      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.02/1.22  thf('69', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.02/1.22      inference('demod', [status(thm)], ['23', '24'])).
% 1.02/1.22  thf('70', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_B @ sk_A)
% 1.02/1.22         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.02/1.22      inference('demod', [status(thm)], ['68', '69'])).
% 1.02/1.22  thf('71', plain,
% 1.02/1.22      (![X19 : $i, X20 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 1.02/1.22           = (k4_xboole_0 @ X19 @ X20))),
% 1.02/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.02/1.22  thf('72', plain,
% 1.02/1.22      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 1.02/1.22         (k2_xboole_0 @ sk_B @ sk_A))
% 1.02/1.22         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.02/1.22      inference('sup+', [status(thm)], ['70', '71'])).
% 1.02/1.22  thf('73', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.02/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.02/1.22  thf('74', plain,
% 1.02/1.22      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.02/1.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.02/1.22  thf('75', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.02/1.22      inference('sup+', [status(thm)], ['73', '74'])).
% 1.02/1.22  thf('76', plain,
% 1.02/1.22      (![X7 : $i, X9 : $i]:
% 1.02/1.22         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 1.02/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.22  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['75', '76'])).
% 1.02/1.22  thf('78', plain,
% 1.02/1.22      (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.02/1.22      inference('demod', [status(thm)], ['72', '77'])).
% 1.02/1.22  thf('79', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.02/1.22          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['26', '27'])).
% 1.02/1.22  thf('80', plain,
% 1.02/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.02/1.22        | (r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 1.02/1.22      inference('sup-', [status(thm)], ['78', '79'])).
% 1.02/1.22  thf('81', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A)),
% 1.02/1.22      inference('simplify', [status(thm)], ['80'])).
% 1.02/1.22  thf('82', plain,
% 1.02/1.22      (![X10 : $i, X11 : $i]:
% 1.02/1.22         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 1.02/1.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.22  thf('83', plain,
% 1.02/1.22      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (sk_A))),
% 1.02/1.22      inference('sup-', [status(thm)], ['81', '82'])).
% 1.02/1.22  thf('84', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.22  thf('85', plain,
% 1.02/1.22      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['83', '84'])).
% 1.02/1.22  thf('86', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 1.02/1.22      inference('demod', [status(thm)], ['11', '16'])).
% 1.02/1.22  thf('87', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.02/1.22           = (X0))),
% 1.02/1.22      inference('demod', [status(thm)], ['45', '50'])).
% 1.02/1.22  thf('88', plain,
% 1.02/1.22      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_D) @ sk_B) = (sk_D))),
% 1.02/1.22      inference('sup+', [status(thm)], ['86', '87'])).
% 1.02/1.22  thf('89', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.02/1.22           = (k4_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('sup+', [status(thm)], ['53', '54'])).
% 1.02/1.22  thf('90', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 1.02/1.22      inference('demod', [status(thm)], ['88', '89'])).
% 1.02/1.22  thf('91', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['85', '90'])).
% 1.02/1.22  thf('92', plain, (((sk_D) = (sk_A))),
% 1.02/1.22      inference('sup+', [status(thm)], ['60', '91'])).
% 1.02/1.22  thf('93', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['17', '92'])).
% 1.02/1.22  thf('94', plain,
% 1.02/1.22      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 1.02/1.22         = (k4_xboole_0 @ sk_C @ sk_D))),
% 1.02/1.22      inference('sup+', [status(thm)], ['61', '62'])).
% 1.02/1.22  thf('95', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['38', '39'])).
% 1.02/1.22  thf('96', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['85', '90'])).
% 1.02/1.22  thf('97', plain,
% 1.02/1.22      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 1.02/1.22           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 1.02/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.22  thf('98', plain,
% 1.02/1.22      (![X24 : $i, X25 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.02/1.22           = (k3_xboole_0 @ X24 @ X25))),
% 1.02/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.22  thf('99', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X2 @ 
% 1.02/1.22           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 1.02/1.22           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.02/1.22      inference('sup+', [status(thm)], ['97', '98'])).
% 1.02/1.22  thf('100', plain,
% 1.02/1.22      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 1.02/1.22           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 1.02/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.22  thf('101', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X2 @ 
% 1.02/1.22           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 1.02/1.22           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.02/1.22      inference('demod', [status(thm)], ['99', '100'])).
% 1.02/1.22  thf('102', plain,
% 1.02/1.22      (![X0 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_A)))
% 1.02/1.22           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_D))),
% 1.02/1.22      inference('sup+', [status(thm)], ['96', '101'])).
% 1.02/1.22  thf('103', plain,
% 1.02/1.22      (![X16 : $i, X17 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 1.02/1.22           = (k2_xboole_0 @ X16 @ X17))),
% 1.02/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.02/1.22  thf('104', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.02/1.22      inference('demod', [status(thm)], ['20', '21'])).
% 1.02/1.22  thf('105', plain,
% 1.02/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.22  thf('106', plain,
% 1.02/1.22      (![X0 : $i]:
% 1.02/1.22         ((k1_xboole_0) = (k3_xboole_0 @ sk_D @ (k4_xboole_0 @ X0 @ sk_A)))),
% 1.02/1.22      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 1.02/1.22  thf('107', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_C))),
% 1.02/1.22      inference('sup+', [status(thm)], ['95', '106'])).
% 1.02/1.22  thf('108', plain,
% 1.02/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.22  thf('109', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 1.02/1.22      inference('demod', [status(thm)], ['107', '108'])).
% 1.02/1.22  thf('110', plain,
% 1.02/1.22      (![X24 : $i, X25 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.02/1.22           = (k3_xboole_0 @ X24 @ X25))),
% 1.02/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.22  thf('111', plain,
% 1.02/1.22      (![X16 : $i, X17 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 1.02/1.22           = (k2_xboole_0 @ X16 @ X17))),
% 1.02/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.02/1.22  thf('112', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.02/1.22           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.02/1.22      inference('sup+', [status(thm)], ['110', '111'])).
% 1.02/1.22  thf('113', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.22  thf('114', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.22  thf('115', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.02/1.22           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('demod', [status(thm)], ['112', '113', '114'])).
% 1.02/1.22  thf('116', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.02/1.22      inference('demod', [status(thm)], ['14', '15'])).
% 1.02/1.22  thf('117', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.02/1.22           = (X1))),
% 1.02/1.22      inference('demod', [status(thm)], ['115', '116'])).
% 1.02/1.22  thf('118', plain,
% 1.02/1.22      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_D)) = (sk_C))),
% 1.02/1.22      inference('sup+', [status(thm)], ['109', '117'])).
% 1.02/1.22  thf('119', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.22  thf(t1_boole, axiom,
% 1.02/1.22    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.22  thf('120', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.02/1.22      inference('cnf', [status(esa)], [t1_boole])).
% 1.02/1.22  thf('121', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.02/1.22      inference('sup+', [status(thm)], ['119', '120'])).
% 1.02/1.22  thf('122', plain, (((k4_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 1.02/1.22      inference('demod', [status(thm)], ['118', '121'])).
% 1.02/1.22  thf('123', plain,
% 1.02/1.22      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D) = (sk_C))),
% 1.02/1.22      inference('demod', [status(thm)], ['94', '122'])).
% 1.02/1.22  thf('124', plain, (((sk_D) = (sk_A))),
% 1.02/1.22      inference('sup+', [status(thm)], ['60', '91'])).
% 1.02/1.22  thf('125', plain,
% 1.02/1.22      (![X19 : $i, X20 : $i]:
% 1.02/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 1.02/1.22           = (k4_xboole_0 @ X19 @ X20))),
% 1.02/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.02/1.22  thf('126', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 1.02/1.22      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.02/1.22  thf('127', plain, (((sk_B) = (sk_C))),
% 1.02/1.22      inference('sup+', [status(thm)], ['93', '126'])).
% 1.02/1.22  thf('128', plain, (((sk_C) != (sk_B))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('129', plain, ($false),
% 1.02/1.22      inference('simplify_reflect-', [status(thm)], ['127', '128'])).
% 1.02/1.22  
% 1.02/1.22  % SZS output end Refutation
% 1.02/1.22  
% 1.06/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
