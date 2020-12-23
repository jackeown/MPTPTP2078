%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jJqunqCsbN

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:50 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 863 expanded)
%              Number of leaves         :   17 ( 259 expanded)
%              Depth                    :   19
%              Number of atoms          :  739 (7915 expanded)
%              Number of equality atoms :  119 (1316 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X17 ) @ ( k1_setfam_1 @ X18 ) ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X19: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('12',plain,(
    ! [X14: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t58_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X15 ) @ X16 )
        = ( k1_tarski @ X15 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t58_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( k1_tarski @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X14: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X17 ) @ ( k1_setfam_1 @ X18 ) ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_setfam_1 @ X1 ) @ ( k1_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X19: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('43',plain,(
    ! [X19: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X1 @ X0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('48',plain,
    ( ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X19: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('50',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_A )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_A )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('52',plain,(
    ! [X14: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('53',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_A )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_A )
    | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('57',plain,(
    ! [X19: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ k1_xboole_0 )
        = X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('63',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('65',plain,(
    ! [X14: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('66',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('70',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_xboole_0 = sk_A )
    | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','70'])).

thf('72',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('73',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','73'])).

thf('75',plain,(
    ! [X14: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('76',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','73'])).

thf('78',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['76','77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jJqunqCsbN
% 0.13/0.36  % Computer   : n016.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:08:34 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 383 iterations in 0.181s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(t41_enumset1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k2_tarski @ A @ B ) =
% 0.47/0.66       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i]:
% 0.47/0.66         ((k2_tarski @ X5 @ X6)
% 0.47/0.66           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.47/0.66  thf(t11_setfam_1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.47/0.66  thf('1', plain, (![X19 : $i]: ((k1_setfam_1 @ (k1_tarski @ X19)) = (X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf(t10_setfam_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.47/0.66            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i]:
% 0.47/0.66         (((X17) = (k1_xboole_0))
% 0.47/0.66          | ((k1_setfam_1 @ (k2_xboole_0 @ X17 @ X18))
% 0.47/0.66              = (k3_xboole_0 @ (k1_setfam_1 @ X17) @ (k1_setfam_1 @ X18)))
% 0.47/0.66          | ((X18) = (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.47/0.66            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.47/0.66          | ((X1) = (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.47/0.66            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.47/0.66          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['0', '3'])).
% 0.47/0.66  thf('5', plain, (![X19 : $i]: ((k1_setfam_1 @ (k1_tarski @ X19)) = (X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.47/0.66          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf(t12_setfam_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i]:
% 0.47/0.66        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.47/0.66         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.47/0.66        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.66        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.66        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.66  thf(t16_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.47/0.66          ( ( A ) = ( B ) ) ) ))).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X13 : $i, X14 : $i]:
% 0.47/0.66         (~ (r1_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14))
% 0.47/0.66          | ((X13) != (X14)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X14 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))),
% 0.47/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.47/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['10', '12'])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '13'])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.66        | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.66  thf(t69_enumset1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.66  thf('16', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.66  thf('17', plain, (![X19 : $i]: ((k1_setfam_1 @ (k1_tarski @ X19)) = (X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.47/0.66          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k1_tarski @ X0) = (k1_xboole_0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.47/0.66  thf(t58_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.47/0.66       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X15 : $i, X16 : $i]:
% 0.47/0.66         (((k3_xboole_0 @ (k1_tarski @ X15) @ X16) = (k1_tarski @ X15))
% 0.47/0.66          | (r1_xboole_0 @ (k1_tarski @ X15) @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [t58_zfmisc_1])).
% 0.47/0.66  thf(d7_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.47/0.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (![X0 : $i, X2 : $i]:
% 0.47/0.66         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.47/0.66          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.47/0.66          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.47/0.66          | ((k1_tarski @ X0) != (k1_xboole_0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['24'])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.66          | ((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.47/0.66          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['21', '25'])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.47/0.66          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['26'])).
% 0.47/0.66  thf('28', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X14 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))),
% 0.47/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('31', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '30'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (![X0 : $i, X2 : $i]:
% 0.47/0.66         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.66  thf('34', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('simplify', [status(thm)], ['33'])).
% 0.47/0.66  thf('35', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['15', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i]:
% 0.47/0.66         ((k2_tarski @ X5 @ X6)
% 0.47/0.66           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i]:
% 0.47/0.66         (((X17) = (k1_xboole_0))
% 0.47/0.66          | ((k1_setfam_1 @ (k2_xboole_0 @ X17 @ X18))
% 0.47/0.66              = (k3_xboole_0 @ (k1_setfam_1 @ X17) @ (k1_setfam_1 @ X18)))
% 0.47/0.66          | ((X18) = (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i, X2 : $i]:
% 0.47/0.66         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.47/0.66          | ((X0) = (k1_xboole_0))
% 0.47/0.66          | ((X1) = (k1_xboole_0))
% 0.47/0.66          | (r1_xboole_0 @ (k1_setfam_1 @ X1) @ (k1_setfam_1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['38', '39'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) != (k1_xboole_0))
% 0.47/0.66          | (r1_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ 
% 0.47/0.66             (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.47/0.66          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['37', '40'])).
% 0.47/0.66  thf('42', plain, (![X19 : $i]: ((k1_setfam_1 @ (k1_tarski @ X19)) = (X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf('43', plain, (![X19 : $i]: ((k1_setfam_1 @ (k1_tarski @ X19)) = (X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) != (k1_xboole_0))
% 0.47/0.66          | (r1_xboole_0 @ X1 @ X0)
% 0.47/0.66          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) != (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.66          | (r1_xboole_0 @ X0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['36', '44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['45'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.66        | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      ((((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.47/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.66  thf('49', plain, (![X19 : $i]: ((k1_setfam_1 @ (k1_tarski @ X19)) = (X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf('50', plain,
% 0.47/0.66      ((((k1_setfam_1 @ k1_xboole_0) = (sk_A))
% 0.47/0.66        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['48', '49'])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      ((((k1_setfam_1 @ k1_xboole_0) = (sk_A))
% 0.47/0.66        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['48', '49'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X14 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))),
% 0.47/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      ((~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0)
% 0.47/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (sk_A))
% 0.47/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['50', '53'])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      ((((k1_setfam_1 @ k1_xboole_0) = (sk_A))
% 0.47/0.66        | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['54'])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k1_tarski @ X0) = (k1_xboole_0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.47/0.66  thf('57', plain, (![X19 : $i]: ((k1_setfam_1 @ (k1_tarski @ X19)) = (X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ k1_xboole_0) = (X0))
% 0.47/0.66          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['56', '57'])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (![X0 : $i, X2 : $i]:
% 0.47/0.66         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.66  thf('60', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) != (k1_xboole_0))
% 0.47/0.66          | ((k1_setfam_1 @ k1_xboole_0) = (X0))
% 0.47/0.66          | (r1_xboole_0 @ X0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.66  thf('61', plain,
% 0.47/0.66      (((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.66        | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.66  thf('63', plain,
% 0.47/0.66      ((((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.47/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      ((((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.47/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      (![X14 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))),
% 0.47/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      ((~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.47/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.47/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['63', '66'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      ((((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.47/0.66        | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['67'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      (((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.66  thf('70', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('clc', [status(thm)], ['68', '69'])).
% 0.47/0.66  thf('71', plain,
% 0.47/0.66      ((((k1_xboole_0) = (sk_A)) | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['55', '70'])).
% 0.47/0.66  thf('72', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('simplify', [status(thm)], ['33'])).
% 0.47/0.66  thf('73', plain, (((k1_xboole_0) = (sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.66  thf('74', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['35', '73'])).
% 0.47/0.66  thf('75', plain,
% 0.47/0.66      (![X14 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))),
% 0.47/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.66  thf('76', plain, (~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.47/0.66      inference('sup-', [status(thm)], ['74', '75'])).
% 0.47/0.66  thf('77', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['35', '73'])).
% 0.47/0.66  thf('78', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('simplify', [status(thm)], ['33'])).
% 0.47/0.66  thf('79', plain, ($false),
% 0.47/0.66      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
