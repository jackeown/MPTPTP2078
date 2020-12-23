%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pCUJWB8soD

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:35 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 161 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  650 (1188 expanded)
%              Number of equality atoms :   65 ( 124 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['6','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['5','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('63',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','61','62'])).

thf('64',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pCUJWB8soD
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.27/1.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.27/1.47  % Solved by: fo/fo7.sh
% 1.27/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.47  % done 1697 iterations in 1.004s
% 1.27/1.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.27/1.47  % SZS output start Refutation
% 1.27/1.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.27/1.47  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.27/1.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.27/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.47  thf(sk_C_type, type, sk_C: $i).
% 1.27/1.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.27/1.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.27/1.47  thf(t81_xboole_1, conjecture,
% 1.27/1.47    (![A:$i,B:$i,C:$i]:
% 1.27/1.47     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.27/1.47       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.27/1.47  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.47    (~( ![A:$i,B:$i,C:$i]:
% 1.27/1.47        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.27/1.47          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 1.27/1.47    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 1.27/1.47  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.27/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.47  thf(t48_xboole_1, axiom,
% 1.27/1.47    (![A:$i,B:$i]:
% 1.27/1.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.27/1.47  thf('1', plain,
% 1.27/1.47      (![X13 : $i, X14 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.27/1.47           = (k3_xboole_0 @ X13 @ X14))),
% 1.27/1.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.47  thf(t41_xboole_1, axiom,
% 1.27/1.47    (![A:$i,B:$i,C:$i]:
% 1.27/1.47     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.27/1.47       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.27/1.47  thf('2', plain,
% 1.27/1.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.27/1.47           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.27/1.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.27/1.47  thf('3', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.27/1.47           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.27/1.47      inference('sup+', [status(thm)], ['1', '2'])).
% 1.27/1.47  thf(t49_xboole_1, axiom,
% 1.27/1.47    (![A:$i,B:$i,C:$i]:
% 1.27/1.47     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.27/1.47       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.27/1.47  thf('4', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('5', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 1.27/1.47           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.27/1.47      inference('demod', [status(thm)], ['3', '4'])).
% 1.27/1.47  thf(commutativity_k2_xboole_0, axiom,
% 1.27/1.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.27/1.47  thf('6', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.27/1.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.27/1.47  thf('7', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.27/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.47  thf(d7_xboole_0, axiom,
% 1.27/1.47    (![A:$i,B:$i]:
% 1.27/1.47     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.27/1.47       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.27/1.47  thf('8', plain,
% 1.27/1.47      (![X2 : $i, X3 : $i]:
% 1.27/1.47         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.27/1.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.47  thf('9', plain,
% 1.27/1.47      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.27/1.47      inference('sup-', [status(thm)], ['7', '8'])).
% 1.27/1.47  thf('10', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('11', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ sk_A @ 
% 1.27/1.47           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 1.27/1.47           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.27/1.47      inference('sup+', [status(thm)], ['9', '10'])).
% 1.27/1.47  thf('12', plain,
% 1.27/1.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.27/1.47           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.27/1.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.27/1.47  thf('13', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ sk_A @ 
% 1.27/1.47           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))
% 1.27/1.47           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.27/1.47      inference('demod', [status(thm)], ['11', '12'])).
% 1.27/1.47  thf(t3_boole, axiom,
% 1.27/1.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.27/1.47  thf('14', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.27/1.47      inference('cnf', [status(esa)], [t3_boole])).
% 1.27/1.47  thf(t79_xboole_1, axiom,
% 1.27/1.47    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.27/1.47  thf('15', plain,
% 1.27/1.47      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 1.27/1.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.27/1.47  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.27/1.47      inference('sup+', [status(thm)], ['14', '15'])).
% 1.27/1.47  thf(symmetry_r1_xboole_0, axiom,
% 1.27/1.47    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.27/1.47  thf('17', plain,
% 1.27/1.47      (![X5 : $i, X6 : $i]:
% 1.27/1.47         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.27/1.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.27/1.47  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.27/1.47      inference('sup-', [status(thm)], ['16', '17'])).
% 1.27/1.47  thf('19', plain,
% 1.27/1.47      (![X2 : $i, X3 : $i]:
% 1.27/1.47         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.27/1.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.47  thf('20', plain,
% 1.27/1.47      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.27/1.47      inference('sup-', [status(thm)], ['18', '19'])).
% 1.27/1.47  thf('21', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('22', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 1.27/1.47           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.27/1.47      inference('sup+', [status(thm)], ['20', '21'])).
% 1.27/1.47  thf('23', plain,
% 1.27/1.47      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.27/1.47      inference('sup-', [status(thm)], ['18', '19'])).
% 1.27/1.47  thf('24', plain,
% 1.27/1.47      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.27/1.47      inference('demod', [status(thm)], ['22', '23'])).
% 1.27/1.47  thf('25', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ sk_A @ 
% 1.27/1.47           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))) = (k1_xboole_0))),
% 1.27/1.47      inference('demod', [status(thm)], ['13', '24'])).
% 1.27/1.47  thf('26', plain,
% 1.27/1.47      (![X13 : $i, X14 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.27/1.47           = (k3_xboole_0 @ X13 @ X14))),
% 1.27/1.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.47  thf('27', plain,
% 1.27/1.47      (![X13 : $i, X14 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.27/1.47           = (k3_xboole_0 @ X13 @ X14))),
% 1.27/1.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.47  thf('28', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.27/1.47           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.27/1.47      inference('sup+', [status(thm)], ['26', '27'])).
% 1.27/1.47  thf('29', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.27/1.47           = (k3_xboole_0 @ sk_A @ 
% 1.27/1.47              (k4_xboole_0 @ sk_A @ 
% 1.27/1.47               (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))))),
% 1.27/1.47      inference('sup+', [status(thm)], ['25', '28'])).
% 1.27/1.47  thf('30', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.27/1.47      inference('cnf', [status(esa)], [t3_boole])).
% 1.27/1.47  thf('31', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((sk_A)
% 1.27/1.47           = (k3_xboole_0 @ sk_A @ 
% 1.27/1.47              (k4_xboole_0 @ sk_A @ 
% 1.27/1.47               (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))))),
% 1.27/1.47      inference('demod', [status(thm)], ['29', '30'])).
% 1.27/1.47  thf('32', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.27/1.47      inference('cnf', [status(esa)], [t3_boole])).
% 1.27/1.47  thf('33', plain,
% 1.27/1.47      (![X13 : $i, X14 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.27/1.47           = (k3_xboole_0 @ X13 @ X14))),
% 1.27/1.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.47  thf('34', plain,
% 1.27/1.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.27/1.47      inference('sup+', [status(thm)], ['32', '33'])).
% 1.27/1.47  thf('35', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.27/1.47      inference('sup+', [status(thm)], ['14', '15'])).
% 1.27/1.47  thf('36', plain,
% 1.27/1.47      (![X2 : $i, X3 : $i]:
% 1.27/1.47         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.27/1.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.47  thf('37', plain,
% 1.27/1.47      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.27/1.47      inference('sup-', [status(thm)], ['35', '36'])).
% 1.27/1.47  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.27/1.47      inference('demod', [status(thm)], ['34', '37'])).
% 1.27/1.47  thf('39', plain,
% 1.27/1.47      (![X13 : $i, X14 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.27/1.47           = (k3_xboole_0 @ X13 @ X14))),
% 1.27/1.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.47  thf('40', plain,
% 1.27/1.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.27/1.47      inference('sup+', [status(thm)], ['38', '39'])).
% 1.27/1.47  thf('41', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.27/1.47      inference('cnf', [status(esa)], [t3_boole])).
% 1.27/1.47  thf('42', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.27/1.47      inference('demod', [status(thm)], ['40', '41'])).
% 1.27/1.47  thf('43', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('44', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.27/1.47           = (k4_xboole_0 @ X0 @ X1))),
% 1.27/1.47      inference('sup+', [status(thm)], ['42', '43'])).
% 1.27/1.47  thf('45', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((sk_A)
% 1.27/1.47           = (k4_xboole_0 @ sk_A @ 
% 1.27/1.47              (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))))),
% 1.27/1.47      inference('demod', [status(thm)], ['31', '44'])).
% 1.27/1.47  thf('46', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((sk_A)
% 1.27/1.47           = (k4_xboole_0 @ sk_A @ 
% 1.27/1.47              (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C))))),
% 1.27/1.47      inference('sup+', [status(thm)], ['6', '45'])).
% 1.27/1.47  thf('47', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((sk_A)
% 1.27/1.47           = (k4_xboole_0 @ sk_A @ 
% 1.27/1.47              (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))))),
% 1.27/1.47      inference('sup+', [status(thm)], ['5', '46'])).
% 1.27/1.47  thf('48', plain,
% 1.27/1.47      (![X13 : $i, X14 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.27/1.47           = (k3_xboole_0 @ X13 @ X14))),
% 1.27/1.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.47  thf('49', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('50', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X2 @ 
% 1.27/1.47           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 1.27/1.47           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.27/1.47      inference('sup+', [status(thm)], ['48', '49'])).
% 1.27/1.47  thf('51', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('52', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X2 @ 
% 1.27/1.47           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 1.27/1.47           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.27/1.47      inference('demod', [status(thm)], ['50', '51'])).
% 1.27/1.47  thf('53', plain,
% 1.27/1.47      (((k3_xboole_0 @ sk_B @ sk_A)
% 1.27/1.47         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 1.27/1.47      inference('sup+', [status(thm)], ['47', '52'])).
% 1.27/1.47  thf('54', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.27/1.47           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.27/1.47      inference('sup+', [status(thm)], ['26', '27'])).
% 1.27/1.47  thf('55', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.27/1.47           = (k4_xboole_0 @ X0 @ X1))),
% 1.27/1.47      inference('sup+', [status(thm)], ['42', '43'])).
% 1.27/1.47  thf('56', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i]:
% 1.27/1.47         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.27/1.47           = (k4_xboole_0 @ X1 @ X0))),
% 1.27/1.47      inference('demod', [status(thm)], ['54', '55'])).
% 1.27/1.47  thf('57', plain,
% 1.27/1.47      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.27/1.47         (k3_xboole_0 @ sk_B @ sk_A))
% 1.27/1.47         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 1.27/1.47      inference('sup+', [status(thm)], ['53', '56'])).
% 1.27/1.47  thf('58', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.27/1.47      inference('demod', [status(thm)], ['34', '37'])).
% 1.27/1.47  thf('60', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('61', plain,
% 1.27/1.47      (![X0 : $i, X1 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.27/1.47           = (k1_xboole_0))),
% 1.27/1.47      inference('sup+', [status(thm)], ['59', '60'])).
% 1.27/1.47  thf('62', plain,
% 1.27/1.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.27/1.47           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.27/1.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.27/1.47  thf('63', plain,
% 1.27/1.47      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.27/1.47      inference('demod', [status(thm)], ['57', '58', '61', '62'])).
% 1.27/1.47  thf('64', plain,
% 1.27/1.47      (![X2 : $i, X4 : $i]:
% 1.27/1.47         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.27/1.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.47  thf('65', plain,
% 1.27/1.47      ((((k1_xboole_0) != (k1_xboole_0))
% 1.27/1.47        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.27/1.47      inference('sup-', [status(thm)], ['63', '64'])).
% 1.27/1.47  thf('66', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.27/1.47      inference('simplify', [status(thm)], ['65'])).
% 1.27/1.47  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 1.27/1.47  
% 1.27/1.47  % SZS output end Refutation
% 1.27/1.47  
% 1.27/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
