%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0kVzDLohq4

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:13 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 151 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  632 (1205 expanded)
%              Number of equality atoms :   60 ( 125 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['14'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['14'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','46','60'])).

thf('62',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0kVzDLohq4
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 1603 iterations in 0.687s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.14  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.90/1.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(t100_xboole_1, conjecture,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i,B:$i]:
% 0.90/1.14        ( ( k4_xboole_0 @ A @ B ) =
% 0.90/1.14          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.90/1.14  thf('0', plain,
% 0.90/1.14      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.90/1.14         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(commutativity_k3_xboole_0, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.90/1.14  thf('1', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.14  thf('2', plain,
% 0.90/1.14      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.90/1.14         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf('3', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.14  thf('4', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.14  thf(t47_xboole_1, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.90/1.14  thf('5', plain,
% 0.90/1.14      (![X14 : $i, X15 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.90/1.14           = (k4_xboole_0 @ X14 @ X15))),
% 0.90/1.14      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.14  thf('6', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.14           = (k4_xboole_0 @ X0 @ X1))),
% 0.90/1.14      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.14  thf(d6_xboole_0, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( k5_xboole_0 @ A @ B ) =
% 0.90/1.14       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.90/1.14  thf('7', plain,
% 0.90/1.14      (![X8 : $i, X9 : $i]:
% 0.90/1.14         ((k5_xboole_0 @ X8 @ X9)
% 0.90/1.14           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 0.90/1.14      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.90/1.14  thf('8', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.90/1.14           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.90/1.14              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.14  thf('9', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.90/1.14           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.90/1.14              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['3', '8'])).
% 0.90/1.14  thf(d5_xboole_0, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.14           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.90/1.14  thf('10', plain,
% 0.90/1.14      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.90/1.14         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.90/1.14          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf(t3_boole, axiom,
% 0.90/1.14    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.14  thf('11', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.90/1.14      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.14  thf('12', plain,
% 0.90/1.14      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X6 @ X5)
% 0.90/1.14          | ~ (r2_hidden @ X6 @ X4)
% 0.90/1.14          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('13', plain,
% 0.90/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X6 @ X4)
% 0.90/1.14          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['12'])).
% 0.90/1.14  thf('14', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['11', '13'])).
% 0.90/1.14  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.14      inference('condensation', [status(thm)], ['14'])).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.90/1.14          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['10', '15'])).
% 0.90/1.14  thf('17', plain,
% 0.90/1.14      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.90/1.14         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.90/1.14          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.90/1.14          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.14      inference('condensation', [status(thm)], ['14'])).
% 0.90/1.14  thf('19', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.90/1.14          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.14  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.14      inference('condensation', [status(thm)], ['14'])).
% 0.90/1.14  thf('21', plain,
% 0.90/1.14      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['19', '20'])).
% 0.90/1.14  thf('22', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.90/1.14          | ((X1) = (k1_xboole_0)))),
% 0.90/1.14      inference('demod', [status(thm)], ['16', '21'])).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      (![X14 : $i, X15 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.90/1.14           = (k4_xboole_0 @ X14 @ X15))),
% 0.90/1.14      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.14  thf(t48_xboole_1, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      (![X16 : $i, X17 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.90/1.14           = (k3_xboole_0 @ X16 @ X17))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.90/1.14           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['23', '24'])).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (![X16 : $i, X17 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.90/1.14           = (k3_xboole_0 @ X16 @ X17))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.14           = (k3_xboole_0 @ X1 @ X0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['25', '26'])).
% 0.90/1.14  thf('28', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.14           = (k4_xboole_0 @ X0 @ X1))),
% 0.90/1.14      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.14  thf('29', plain,
% 0.90/1.14      (![X14 : $i, X15 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.90/1.14           = (k4_xboole_0 @ X14 @ X15))),
% 0.90/1.14      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.14  thf('30', plain,
% 0.90/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X6 @ X4)
% 0.90/1.14          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['12'])).
% 0.90/1.14  thf('31', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.90/1.14          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.14  thf('32', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.90/1.14          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['28', '31'])).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X2 @ 
% 0.90/1.14             (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 0.90/1.14          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['27', '32'])).
% 0.90/1.14  thf('34', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.90/1.14      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.14  thf('35', plain,
% 0.90/1.14      (![X16 : $i, X17 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.90/1.14           = (k3_xboole_0 @ X16 @ X17))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.14  thf('36', plain,
% 0.90/1.14      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['34', '35'])).
% 0.90/1.14  thf('37', plain,
% 0.90/1.14      (![X14 : $i, X15 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.90/1.14           = (k4_xboole_0 @ X14 @ X15))),
% 0.90/1.14      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.14  thf('38', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.90/1.14           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.90/1.14  thf('39', plain,
% 0.90/1.14      (![X16 : $i, X17 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.90/1.14           = (k3_xboole_0 @ X16 @ X17))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.14  thf('40', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.90/1.14      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.14  thf('41', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.90/1.14  thf('42', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.14          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.90/1.14      inference('demod', [status(thm)], ['33', '41'])).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X6 @ X5)
% 0.90/1.14          | (r2_hidden @ X6 @ X3)
% 0.90/1.14          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.90/1.14         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['43'])).
% 0.90/1.14  thf('45', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.90/1.14      inference('clc', [status(thm)], ['42', '44'])).
% 0.90/1.14  thf('46', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['22', '45'])).
% 0.90/1.14  thf('47', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.90/1.14  thf(t41_xboole_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.14       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.90/1.14  thf('48', plain,
% 0.90/1.14      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.90/1.14           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.90/1.14  thf('49', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.90/1.14      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.90/1.14           = (k4_xboole_0 @ X1 @ X0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['48', '49'])).
% 0.90/1.14  thf('51', plain,
% 0.90/1.14      (![X16 : $i, X17 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.90/1.14           = (k3_xboole_0 @ X16 @ X17))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.14  thf('52', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.90/1.14           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['50', '51'])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      (![X16 : $i, X17 : $i]:
% 0.90/1.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.90/1.14           = (k3_xboole_0 @ X16 @ X17))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.14  thf('54', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k3_xboole_0 @ X1 @ X0)
% 0.90/1.14           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.90/1.14      inference('demod', [status(thm)], ['52', '53'])).
% 0.90/1.14  thf('55', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.90/1.14           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['47', '54'])).
% 0.90/1.14  thf('56', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.14  thf('57', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k3_xboole_0 @ X1 @ X0)
% 0.90/1.14           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.90/1.14      inference('demod', [status(thm)], ['52', '53'])).
% 0.90/1.14  thf('58', plain,
% 0.90/1.14      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.14      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.90/1.14  thf('59', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.90/1.14  thf('60', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '59'])).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.90/1.14           = (k4_xboole_0 @ X1 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['9', '46', '60'])).
% 0.90/1.14  thf('62', plain,
% 0.90/1.14      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['2', '61'])).
% 0.90/1.14  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
