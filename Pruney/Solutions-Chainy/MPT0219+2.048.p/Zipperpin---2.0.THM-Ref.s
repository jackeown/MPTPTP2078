%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xcOyo8u5D6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:10 EST 2020

% Result     : Theorem 5.72s
% Output     : Refutation 5.72s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 688 expanded)
%              Number of leaves         :   23 ( 217 expanded)
%              Depth                    :   25
%              Number of atoms          : 1140 (5626 expanded)
%              Number of equality atoms :   95 ( 496 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( X42 = X39 )
      | ( X41
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42 = X39 )
      | ~ ( r2_hidden @ X42 @ ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X24: $i] :
      ( r1_tarski @ k1_xboole_0 @ X24 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('35',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('52',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('59',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X40 != X39 )
      | ( r2_hidden @ X40 @ X41 )
      | ( X41
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('60',plain,(
    ! [X39: $i] :
      ( r2_hidden @ X39 @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X17 ) )
      | ( r2_hidden @ X14 @ X17 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['66'])).

thf('68',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42 = X39 )
      | ~ ( r2_hidden @ X42 @ ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['66'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('77',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['78'])).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ~ ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ~ ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) @ ( k1_tarski @ X0 ) ) @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['57','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','88'])).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X39: $i] :
      ( r2_hidden @ X39 @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('93',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X17 ) )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','96'])).

thf('98',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42 = X39 )
      | ~ ( r2_hidden @ X42 @ ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('100',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xcOyo8u5D6
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.72/5.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.72/5.90  % Solved by: fo/fo7.sh
% 5.72/5.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.72/5.90  % done 3972 iterations in 5.437s
% 5.72/5.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.72/5.90  % SZS output start Refutation
% 5.72/5.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.72/5.90  thf(sk_B_type, type, sk_B: $i).
% 5.72/5.90  thf(sk_A_type, type, sk_A: $i).
% 5.72/5.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.72/5.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.72/5.90  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.72/5.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.72/5.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.72/5.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.72/5.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.72/5.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.72/5.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.72/5.90  thf(t13_zfmisc_1, conjecture,
% 5.72/5.90    (![A:$i,B:$i]:
% 5.72/5.90     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 5.72/5.90         ( k1_tarski @ A ) ) =>
% 5.72/5.90       ( ( A ) = ( B ) ) ))).
% 5.72/5.90  thf(zf_stmt_0, negated_conjecture,
% 5.72/5.90    (~( ![A:$i,B:$i]:
% 5.72/5.90        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 5.72/5.90            ( k1_tarski @ A ) ) =>
% 5.72/5.90          ( ( A ) = ( B ) ) ) )),
% 5.72/5.90    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 5.72/5.90  thf('0', plain,
% 5.72/5.90      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 5.72/5.90         = (k1_tarski @ sk_A))),
% 5.72/5.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.72/5.90  thf(d4_xboole_0, axiom,
% 5.72/5.90    (![A:$i,B:$i,C:$i]:
% 5.72/5.90     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 5.72/5.90       ( ![D:$i]:
% 5.72/5.90         ( ( r2_hidden @ D @ C ) <=>
% 5.72/5.90           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.72/5.90  thf('1', plain,
% 5.72/5.90      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.90         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 5.72/5.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.72/5.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.90      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.72/5.90  thf(d1_tarski, axiom,
% 5.72/5.90    (![A:$i,B:$i]:
% 5.72/5.90     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 5.72/5.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 5.72/5.90  thf('2', plain,
% 5.72/5.90      (![X39 : $i, X41 : $i, X42 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X42 @ X41)
% 5.72/5.90          | ((X42) = (X39))
% 5.72/5.90          | ((X41) != (k1_tarski @ X39)))),
% 5.72/5.90      inference('cnf', [status(esa)], [d1_tarski])).
% 5.72/5.90  thf('3', plain,
% 5.72/5.90      (![X39 : $i, X42 : $i]:
% 5.72/5.90         (((X42) = (X39)) | ~ (r2_hidden @ X42 @ (k1_tarski @ X39)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['2'])).
% 5.72/5.90  thf('4', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_D @ X2 @ (k1_tarski @ X0) @ X1) @ X2)
% 5.72/5.90          | ((X2) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.72/5.90          | ((sk_D @ X2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['1', '3'])).
% 5.72/5.90  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.72/5.90  thf('5', plain, (![X24 : $i]: (r1_tarski @ k1_xboole_0 @ X24)),
% 5.72/5.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.72/5.90  thf(t28_xboole_1, axiom,
% 5.72/5.90    (![A:$i,B:$i]:
% 5.72/5.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.72/5.90  thf('6', plain,
% 5.72/5.90      (![X22 : $i, X23 : $i]:
% 5.72/5.90         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 5.72/5.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.72/5.90  thf('7', plain,
% 5.72/5.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['5', '6'])).
% 5.72/5.90  thf(t100_xboole_1, axiom,
% 5.72/5.90    (![A:$i,B:$i]:
% 5.72/5.90     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.72/5.90  thf('8', plain,
% 5.72/5.90      (![X20 : $i, X21 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ X20 @ X21)
% 5.72/5.90           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 5.72/5.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.72/5.90  thf('9', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 5.72/5.90           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['7', '8'])).
% 5.72/5.90  thf('10', plain,
% 5.72/5.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['5', '6'])).
% 5.72/5.90  thf(commutativity_k3_xboole_0, axiom,
% 5.72/5.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.72/5.90  thf('11', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.72/5.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.72/5.90  thf('12', plain,
% 5.72/5.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['10', '11'])).
% 5.72/5.90  thf('13', plain,
% 5.72/5.90      (![X20 : $i, X21 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ X20 @ X21)
% 5.72/5.90           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 5.72/5.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.72/5.90  thf('14', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['12', '13'])).
% 5.72/5.90  thf(d5_xboole_0, axiom,
% 5.72/5.90    (![A:$i,B:$i,C:$i]:
% 5.72/5.90     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.72/5.90       ( ![D:$i]:
% 5.72/5.90         ( ( r2_hidden @ D @ C ) <=>
% 5.72/5.90           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.72/5.90  thf('15', plain,
% 5.72/5.90      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X12 @ X11)
% 5.72/5.90          | ~ (r2_hidden @ X12 @ X10)
% 5.72/5.90          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 5.72/5.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.90  thf('16', plain,
% 5.72/5.90      (![X9 : $i, X10 : $i, X12 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X12 @ X10)
% 5.72/5.90          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['15'])).
% 5.72/5.90  thf('17', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 5.72/5.90          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['14', '16'])).
% 5.72/5.90  thf('18', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 5.72/5.90          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['9', '17'])).
% 5.72/5.90  thf('19', plain,
% 5.72/5.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['5', '6'])).
% 5.72/5.90  thf('20', plain,
% 5.72/5.90      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X6 @ X5)
% 5.72/5.90          | (r2_hidden @ X6 @ X4)
% 5.72/5.90          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 5.72/5.90      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.72/5.90  thf('21', plain,
% 5.72/5.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.72/5.90         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['20'])).
% 5.72/5.90  thf('22', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['19', '21'])).
% 5.72/5.90  thf('23', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.90      inference('clc', [status(thm)], ['18', '22'])).
% 5.72/5.90  thf('24', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (((sk_D @ k1_xboole_0 @ (k1_tarski @ X1) @ X0) = (X1))
% 5.72/5.90          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 5.72/5.90      inference('sup-', [status(thm)], ['4', '23'])).
% 5.72/5.90  thf('25', plain,
% 5.72/5.90      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.90         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 5.72/5.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.72/5.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.90      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.72/5.90  thf('26', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.90      inference('clc', [status(thm)], ['18', '22'])).
% 5.72/5.90  thf('27', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.72/5.90          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['25', '26'])).
% 5.72/5.90  thf('28', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ X0 @ X1)
% 5.72/5.90          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.72/5.90          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 5.72/5.90      inference('sup+', [status(thm)], ['24', '27'])).
% 5.72/5.90  thf('29', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.72/5.90          | (r2_hidden @ X0 @ X1))),
% 5.72/5.90      inference('simplify', [status(thm)], ['28'])).
% 5.72/5.90  thf('30', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.72/5.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.72/5.90  thf('31', plain,
% 5.72/5.90      (![X20 : $i, X21 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ X20 @ X21)
% 5.72/5.90           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 5.72/5.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.72/5.90  thf('32', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ X0 @ X1)
% 5.72/5.90           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.72/5.90      inference('sup+', [status(thm)], ['30', '31'])).
% 5.72/5.90  thf('33', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 5.72/5.90            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 5.72/5.90          | (r2_hidden @ X0 @ X1))),
% 5.72/5.90      inference('sup+', [status(thm)], ['29', '32'])).
% 5.72/5.90  thf(t2_tarski, axiom,
% 5.72/5.90    (![A:$i,B:$i]:
% 5.72/5.90     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 5.72/5.90       ( ( A ) = ( B ) ) ))).
% 5.72/5.90  thf('34', plain,
% 5.72/5.90      (![X18 : $i, X19 : $i]:
% 5.72/5.90         (((X19) = (X18))
% 5.72/5.90          | (r2_hidden @ (sk_C @ X18 @ X19) @ X18)
% 5.72/5.90          | (r2_hidden @ (sk_C @ X18 @ X19) @ X19))),
% 5.72/5.90      inference('cnf', [status(esa)], [t2_tarski])).
% 5.72/5.90  thf('35', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.90      inference('clc', [status(thm)], ['18', '22'])).
% 5.72/5.90  thf('36', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['34', '35'])).
% 5.72/5.90  thf('37', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 5.72/5.90           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['7', '8'])).
% 5.72/5.90  thf(t1_xboole_0, axiom,
% 5.72/5.90    (![A:$i,B:$i,C:$i]:
% 5.72/5.90     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 5.72/5.90       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 5.72/5.90  thf('38', plain,
% 5.72/5.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X14 @ X15)
% 5.72/5.90          | ~ (r2_hidden @ X14 @ X16)
% 5.72/5.90          | ~ (r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 5.72/5.90      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.72/5.90  thf('39', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 5.72/5.90          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 5.72/5.90          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['37', '38'])).
% 5.72/5.90  thf('40', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 5.72/5.90          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['39'])).
% 5.72/5.90  thf('41', plain,
% 5.72/5.90      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X12 @ X11)
% 5.72/5.90          | (r2_hidden @ X12 @ X9)
% 5.72/5.90          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 5.72/5.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.90  thf('42', plain,
% 5.72/5.90      (![X9 : $i, X10 : $i, X12 : $i]:
% 5.72/5.90         ((r2_hidden @ X12 @ X9)
% 5.72/5.90          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['41'])).
% 5.72/5.90  thf('43', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 5.72/5.90      inference('clc', [status(thm)], ['40', '42'])).
% 5.72/5.90  thf('44', plain,
% 5.72/5.90      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['36', '43'])).
% 5.72/5.90  thf(t98_xboole_1, axiom,
% 5.72/5.90    (![A:$i,B:$i]:
% 5.72/5.90     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 5.72/5.90  thf('45', plain,
% 5.72/5.90      (![X25 : $i, X26 : $i]:
% 5.72/5.90         ((k2_xboole_0 @ X25 @ X26)
% 5.72/5.90           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 5.72/5.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.72/5.90  thf('46', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['44', '45'])).
% 5.72/5.90  thf('47', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 5.72/5.90            = (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 5.72/5.90          | (r2_hidden @ X0 @ X1))),
% 5.72/5.90      inference('demod', [status(thm)], ['33', '46'])).
% 5.72/5.90  thf('48', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['12', '13'])).
% 5.72/5.90  thf('49', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['44', '45'])).
% 5.72/5.90  thf('50', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.90      inference('demod', [status(thm)], ['48', '49'])).
% 5.72/5.90  thf('51', plain,
% 5.72/5.90      (![X18 : $i, X19 : $i]:
% 5.72/5.90         (((X19) = (X18))
% 5.72/5.90          | (r2_hidden @ (sk_C @ X18 @ X19) @ X18)
% 5.72/5.90          | (r2_hidden @ (sk_C @ X18 @ X19) @ X19))),
% 5.72/5.90      inference('cnf', [status(esa)], [t2_tarski])).
% 5.72/5.90  thf('52', plain,
% 5.72/5.90      (![X9 : $i, X10 : $i, X12 : $i]:
% 5.72/5.90         ((r2_hidden @ X12 @ X9)
% 5.72/5.90          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['41'])).
% 5.72/5.90  thf('53', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X2)
% 5.72/5.90          | ((X2) = (k4_xboole_0 @ X1 @ X0))
% 5.72/5.90          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 5.72/5.90      inference('sup-', [status(thm)], ['51', '52'])).
% 5.72/5.90  thf('54', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ X0 @ X1) @ X0) @ X0)
% 5.72/5.90          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.90      inference('eq_fact', [status(thm)], ['53'])).
% 5.72/5.90  thf('55', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_C @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) @ X0)
% 5.72/5.90          | ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.72/5.90      inference('sup+', [status(thm)], ['50', '54'])).
% 5.72/5.90  thf('56', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.90      inference('demod', [status(thm)], ['48', '49'])).
% 5.72/5.90  thf('57', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_C @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) @ X0)
% 5.72/5.90          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.72/5.90      inference('demod', [status(thm)], ['55', '56'])).
% 5.72/5.90  thf('58', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['44', '45'])).
% 5.72/5.90  thf('59', plain,
% 5.72/5.90      (![X39 : $i, X40 : $i, X41 : $i]:
% 5.72/5.90         (((X40) != (X39))
% 5.72/5.90          | (r2_hidden @ X40 @ X41)
% 5.72/5.90          | ((X41) != (k1_tarski @ X39)))),
% 5.72/5.90      inference('cnf', [status(esa)], [d1_tarski])).
% 5.72/5.90  thf('60', plain, (![X39 : $i]: (r2_hidden @ X39 @ (k1_tarski @ X39))),
% 5.72/5.90      inference('simplify', [status(thm)], ['59'])).
% 5.72/5.90  thf('61', plain,
% 5.72/5.90      (![X14 : $i, X15 : $i, X17 : $i]:
% 5.72/5.90         ((r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X17))
% 5.72/5.90          | (r2_hidden @ X14 @ X17)
% 5.72/5.90          | ~ (r2_hidden @ X14 @ X15))),
% 5.72/5.90      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.72/5.90  thf('62', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ X0 @ X1)
% 5.72/5.90          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['60', '61'])).
% 5.72/5.90  thf('63', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 5.72/5.90          | (r2_hidden @ X0 @ k1_xboole_0))),
% 5.72/5.90      inference('sup+', [status(thm)], ['58', '62'])).
% 5.72/5.90  thf('64', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.90      inference('clc', [status(thm)], ['18', '22'])).
% 5.72/5.90  thf('65', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 5.72/5.90      inference('clc', [status(thm)], ['63', '64'])).
% 5.72/5.90  thf('66', plain,
% 5.72/5.90      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.90         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 5.72/5.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.72/5.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.90      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.72/5.90  thf('67', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.72/5.90          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.72/5.90      inference('eq_fact', [status(thm)], ['66'])).
% 5.72/5.90  thf('68', plain,
% 5.72/5.90      (![X39 : $i, X42 : $i]:
% 5.72/5.90         (((X42) = (X39)) | ~ (r2_hidden @ X42 @ (k1_tarski @ X39)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['2'])).
% 5.72/5.90  thf('69', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.72/5.90          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['67', '68'])).
% 5.72/5.90  thf('70', plain,
% 5.72/5.90      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.90         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 5.72/5.90          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.72/5.90          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.72/5.90          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.90      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.72/5.90  thf('71', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X0 @ X1)
% 5.72/5.90          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.72/5.90          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 5.72/5.90               (k1_tarski @ X0))
% 5.72/5.90          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 5.72/5.90               (k1_tarski @ X0))
% 5.72/5.90          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['69', '70'])).
% 5.72/5.90  thf('72', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 5.72/5.90             (k1_tarski @ X0))
% 5.72/5.90          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.72/5.90          | ~ (r2_hidden @ X0 @ X1))),
% 5.72/5.90      inference('simplify', [status(thm)], ['71'])).
% 5.72/5.90  thf('73', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.72/5.90          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.72/5.90      inference('eq_fact', [status(thm)], ['66'])).
% 5.72/5.90  thf('74', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ X0 @ X1)
% 5.72/5.90          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.72/5.90      inference('clc', [status(thm)], ['72', '73'])).
% 5.72/5.90  thf('75', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k1_tarski @ X0)
% 5.72/5.90           = (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 5.72/5.90              (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['65', '74'])).
% 5.72/5.90  thf('76', plain,
% 5.72/5.90      (![X18 : $i, X19 : $i]:
% 5.72/5.90         (((X19) = (X18))
% 5.72/5.90          | (r2_hidden @ (sk_C @ X18 @ X19) @ X18)
% 5.72/5.90          | (r2_hidden @ (sk_C @ X18 @ X19) @ X19))),
% 5.72/5.90      inference('cnf', [status(esa)], [t2_tarski])).
% 5.72/5.90  thf('77', plain,
% 5.72/5.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.72/5.90         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['20'])).
% 5.72/5.90  thf('78', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 5.72/5.90          | ((k3_xboole_0 @ X1 @ X0) = (X2))
% 5.72/5.90          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 5.72/5.90      inference('sup-', [status(thm)], ['76', '77'])).
% 5.72/5.90  thf('79', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ (sk_C @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 5.72/5.90          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 5.72/5.90      inference('eq_fact', [status(thm)], ['78'])).
% 5.72/5.90  thf('80', plain,
% 5.72/5.90      (![X18 : $i, X19 : $i]:
% 5.72/5.90         (((X19) = (X18))
% 5.72/5.90          | ~ (r2_hidden @ (sk_C @ X18 @ X19) @ X18)
% 5.72/5.90          | ~ (r2_hidden @ (sk_C @ X18 @ X19) @ X19))),
% 5.72/5.90      inference('cnf', [status(esa)], [t2_tarski])).
% 5.72/5.90  thf('81', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (((k3_xboole_0 @ X1 @ X0) = (X0))
% 5.72/5.90          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.72/5.90               (k3_xboole_0 @ X1 @ X0))
% 5.72/5.90          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['79', '80'])).
% 5.72/5.90  thf('82', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (~ (r2_hidden @ (sk_C @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.72/5.90             (k3_xboole_0 @ X1 @ X0))
% 5.72/5.90          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['81'])).
% 5.72/5.90  thf('83', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         (~ (r2_hidden @ 
% 5.72/5.90             (sk_C @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) @ 
% 5.72/5.90              (k1_tarski @ X0)) @ 
% 5.72/5.90             (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 5.72/5.90              (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))
% 5.72/5.90          | ((k3_xboole_0 @ (k1_tarski @ X0) @ 
% 5.72/5.90              (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 5.72/5.90              = (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['75', '82'])).
% 5.72/5.90  thf('84', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k1_tarski @ X0)
% 5.72/5.90           = (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 5.72/5.90              (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['65', '74'])).
% 5.72/5.90  thf('85', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k1_tarski @ X0)
% 5.72/5.90           = (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 5.72/5.90              (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['65', '74'])).
% 5.72/5.90  thf('86', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         (~ (r2_hidden @ 
% 5.72/5.90             (sk_C @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) @ 
% 5.72/5.90              (k1_tarski @ X0)) @ 
% 5.72/5.90             (k1_tarski @ X0))
% 5.72/5.90          | ((k1_tarski @ X0) = (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 5.72/5.90      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.72/5.90  thf('87', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         (((k1_tarski @ X0) = (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 5.72/5.90          | ((k1_tarski @ X0) = (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 5.72/5.90      inference('sup-', [status(thm)], ['57', '86'])).
% 5.72/5.90  thf('88', plain,
% 5.72/5.90      (![X0 : $i]:
% 5.72/5.90         ((k1_tarski @ X0) = (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 5.72/5.90      inference('simplify', [status(thm)], ['87'])).
% 5.72/5.90  thf('89', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 5.72/5.90          | (r2_hidden @ X0 @ X1))),
% 5.72/5.90      inference('demod', [status(thm)], ['47', '88'])).
% 5.72/5.90  thf('90', plain,
% 5.72/5.90      (![X25 : $i, X26 : $i]:
% 5.72/5.90         ((k2_xboole_0 @ X25 @ X26)
% 5.72/5.90           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 5.72/5.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.72/5.90  thf('91', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 5.72/5.90            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.72/5.90          | (r2_hidden @ X0 @ X1))),
% 5.72/5.90      inference('sup+', [status(thm)], ['89', '90'])).
% 5.72/5.90  thf('92', plain, (![X39 : $i]: (r2_hidden @ X39 @ (k1_tarski @ X39))),
% 5.72/5.90      inference('simplify', [status(thm)], ['59'])).
% 5.72/5.90  thf('93', plain,
% 5.72/5.90      (![X14 : $i, X15 : $i, X17 : $i]:
% 5.72/5.90         ((r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X17))
% 5.72/5.90          | (r2_hidden @ X14 @ X15)
% 5.72/5.90          | ~ (r2_hidden @ X14 @ X17))),
% 5.72/5.90      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.72/5.90  thf('94', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ X0 @ X1)
% 5.72/5.90          | (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 5.72/5.90      inference('sup-', [status(thm)], ['92', '93'])).
% 5.72/5.90  thf('95', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.72/5.90          | (r2_hidden @ X0 @ X1)
% 5.72/5.90          | (r2_hidden @ X0 @ X1))),
% 5.72/5.90      inference('sup+', [status(thm)], ['91', '94'])).
% 5.72/5.90  thf('96', plain,
% 5.72/5.90      (![X0 : $i, X1 : $i]:
% 5.72/5.90         ((r2_hidden @ X0 @ X1)
% 5.72/5.90          | (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 5.72/5.90      inference('simplify', [status(thm)], ['95'])).
% 5.72/5.90  thf('97', plain,
% 5.72/5.90      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 5.72/5.90        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 5.72/5.90      inference('sup+', [status(thm)], ['0', '96'])).
% 5.72/5.90  thf('98', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 5.72/5.90      inference('simplify', [status(thm)], ['97'])).
% 5.72/5.90  thf('99', plain,
% 5.72/5.90      (![X39 : $i, X42 : $i]:
% 5.72/5.90         (((X42) = (X39)) | ~ (r2_hidden @ X42 @ (k1_tarski @ X39)))),
% 5.72/5.90      inference('simplify', [status(thm)], ['2'])).
% 5.72/5.90  thf('100', plain, (((sk_B) = (sk_A))),
% 5.72/5.90      inference('sup-', [status(thm)], ['98', '99'])).
% 5.72/5.90  thf('101', plain, (((sk_A) != (sk_B))),
% 5.72/5.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.72/5.90  thf('102', plain, ($false),
% 5.72/5.90      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 5.72/5.90  
% 5.72/5.90  % SZS output end Refutation
% 5.72/5.90  
% 5.72/5.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
