%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wkoQxldDnB

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:30 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 275 expanded)
%              Number of leaves         :   18 (  86 expanded)
%              Depth                    :   21
%              Number of atoms          :  678 (2277 expanded)
%              Number of equality atoms :   73 ( 245 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18 != X17 )
      | ( r2_hidden @ X18 @ X19 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X17: $i] :
      ( r2_hidden @ X17 @ ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['12'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k5_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['24','39'])).

thf('41',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','51'])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('59',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('63',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wkoQxldDnB
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.62/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.82  % Solved by: fo/fo7.sh
% 0.62/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.82  % done 635 iterations in 0.375s
% 0.62/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.82  % SZS output start Refutation
% 0.62/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.82  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.62/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.62/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.82  thf(d1_tarski, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.62/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.62/0.82  thf('0', plain,
% 0.62/0.82      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.62/0.82         (((X18) != (X17))
% 0.62/0.82          | (r2_hidden @ X18 @ X19)
% 0.62/0.82          | ((X19) != (k1_tarski @ X17)))),
% 0.62/0.82      inference('cnf', [status(esa)], [d1_tarski])).
% 0.62/0.82  thf('1', plain, (![X17 : $i]: (r2_hidden @ X17 @ (k1_tarski @ X17))),
% 0.62/0.82      inference('simplify', [status(thm)], ['0'])).
% 0.62/0.82  thf(d5_xboole_0, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i]:
% 0.62/0.82     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.62/0.82       ( ![D:$i]:
% 0.62/0.82         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.82           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.62/0.82  thf('2', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X0 @ X1)
% 0.62/0.82          | (r2_hidden @ X0 @ X2)
% 0.62/0.82          | (r2_hidden @ X0 @ X3)
% 0.62/0.82          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.82  thf('3', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.62/0.82          | (r2_hidden @ X0 @ X2)
% 0.62/0.82          | ~ (r2_hidden @ X0 @ X1))),
% 0.62/0.82      inference('simplify', [status(thm)], ['2'])).
% 0.62/0.82  thf('4', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((r2_hidden @ X0 @ X1)
% 0.62/0.82          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['1', '3'])).
% 0.62/0.82  thf('5', plain,
% 0.62/0.82      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.62/0.82         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.62/0.82          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.62/0.82          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.62/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.82  thf(d10_xboole_0, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.82  thf('6', plain,
% 0.62/0.82      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.62/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.82  thf('7', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.62/0.82      inference('simplify', [status(thm)], ['6'])).
% 0.62/0.82  thf(l32_xboole_1, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.62/0.82  thf('8', plain,
% 0.62/0.82      (![X9 : $i, X11 : $i]:
% 0.62/0.82         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.62/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.62/0.82  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.82  thf('10', plain,
% 0.62/0.82      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X4 @ X3)
% 0.62/0.82          | ~ (r2_hidden @ X4 @ X2)
% 0.62/0.82          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.82  thf('11', plain,
% 0.62/0.82      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X4 @ X2)
% 0.62/0.82          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('simplify', [status(thm)], ['10'])).
% 0.62/0.82  thf('12', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.62/0.82      inference('sup-', [status(thm)], ['9', '11'])).
% 0.62/0.82  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.62/0.82      inference('condensation', [status(thm)], ['12'])).
% 0.62/0.82  thf('14', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.62/0.82          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['5', '13'])).
% 0.62/0.82  thf('15', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.62/0.82          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['5', '13'])).
% 0.62/0.82  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.62/0.82      inference('condensation', [status(thm)], ['12'])).
% 0.62/0.82  thf('17', plain,
% 0.62/0.82      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.62/0.82      inference('sup-', [status(thm)], ['15', '16'])).
% 0.62/0.82  thf('18', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.62/0.82          | ((X1) = (k1_xboole_0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['14', '17'])).
% 0.62/0.82  thf('19', plain,
% 0.62/0.82      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X4 @ X3)
% 0.62/0.82          | (r2_hidden @ X4 @ X1)
% 0.62/0.82          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.82  thf('20', plain,
% 0.62/0.82      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.62/0.82         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('simplify', [status(thm)], ['19'])).
% 0.62/0.82  thf('21', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.62/0.82          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 0.62/0.82             X1))),
% 0.62/0.82      inference('sup-', [status(thm)], ['18', '20'])).
% 0.62/0.82  thf('22', plain,
% 0.62/0.82      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X20 @ X19)
% 0.62/0.82          | ((X20) = (X17))
% 0.62/0.82          | ((X19) != (k1_tarski @ X17)))),
% 0.62/0.82      inference('cnf', [status(esa)], [d1_tarski])).
% 0.62/0.82  thf('23', plain,
% 0.62/0.82      (![X17 : $i, X20 : $i]:
% 0.62/0.82         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.62/0.82      inference('simplify', [status(thm)], ['22'])).
% 0.62/0.82  thf('24', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 0.62/0.82          | ((sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 0.62/0.82              = (X0)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['21', '23'])).
% 0.62/0.82  thf('25', plain,
% 0.62/0.82      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.62/0.82         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.62/0.82          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.62/0.82          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.62/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.82  thf('26', plain,
% 0.62/0.82      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.62/0.82         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.62/0.82          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.62/0.82          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.62/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.82  thf('27', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.62/0.82          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.62/0.82          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.62/0.82          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.62/0.82  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.82  thf(t48_xboole_1, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.62/0.82  thf('29', plain,
% 0.62/0.82      (![X15 : $i, X16 : $i]:
% 0.62/0.82         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.62/0.82           = (k3_xboole_0 @ X15 @ X16))),
% 0.62/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.82  thf('30', plain,
% 0.62/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['28', '29'])).
% 0.62/0.82  thf(t3_boole, axiom,
% 0.62/0.82    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.62/0.82  thf('31', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.62/0.82      inference('cnf', [status(esa)], [t3_boole])).
% 0.62/0.82  thf('32', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.62/0.82      inference('demod', [status(thm)], ['30', '31'])).
% 0.62/0.82  thf(t100_xboole_1, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.62/0.82  thf('33', plain,
% 0.62/0.82      (![X12 : $i, X13 : $i]:
% 0.62/0.82         ((k4_xboole_0 @ X12 @ X13)
% 0.62/0.82           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.82  thf('34', plain,
% 0.62/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['32', '33'])).
% 0.62/0.82  thf('35', plain,
% 0.62/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['32', '33'])).
% 0.62/0.82  thf('36', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.62/0.82          | ((X1) = (k5_xboole_0 @ X0 @ X0))
% 0.62/0.82          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.62/0.82          | ((X1) = (k5_xboole_0 @ X0 @ X0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['27', '34', '35'])).
% 0.62/0.82  thf('37', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (((X1) = (k5_xboole_0 @ X0 @ X0))
% 0.62/0.82          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.62/0.82      inference('simplify', [status(thm)], ['36'])).
% 0.62/0.82  thf('38', plain,
% 0.62/0.82      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X4 @ X2)
% 0.62/0.82          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('simplify', [status(thm)], ['10'])).
% 0.62/0.82  thf('39', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         (((k4_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X2 @ X2))
% 0.62/0.82          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.62/0.82      inference('sup-', [status(thm)], ['37', '38'])).
% 0.62/0.82  thf('40', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X0 @ X1)
% 0.62/0.82          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.62/0.82          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.62/0.82              = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['24', '39'])).
% 0.62/0.82  thf('41', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.62/0.82      inference('cnf', [status(esa)], [t3_boole])).
% 0.62/0.82  thf('42', plain,
% 0.62/0.82      (![X15 : $i, X16 : $i]:
% 0.62/0.82         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.62/0.82           = (k3_xboole_0 @ X15 @ X16))),
% 0.62/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.82  thf('43', plain,
% 0.62/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['41', '42'])).
% 0.62/0.82  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.82  thf('45', plain,
% 0.62/0.82      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.82      inference('demod', [status(thm)], ['43', '44'])).
% 0.62/0.82  thf('46', plain,
% 0.62/0.82      (![X12 : $i, X13 : $i]:
% 0.62/0.82         ((k4_xboole_0 @ X12 @ X13)
% 0.62/0.82           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.82  thf('47', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['45', '46'])).
% 0.62/0.82  thf('48', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.62/0.82      inference('cnf', [status(esa)], [t3_boole])).
% 0.62/0.82  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['47', '48'])).
% 0.62/0.82  thf('50', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X0 @ X1)
% 0.62/0.82          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.62/0.82          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['40', '49'])).
% 0.62/0.82  thf('51', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.62/0.82          | ~ (r2_hidden @ X0 @ X1))),
% 0.62/0.82      inference('simplify', [status(thm)], ['50'])).
% 0.62/0.82  thf('52', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((r2_hidden @ X1 @ X0)
% 0.62/0.82          | ((k4_xboole_0 @ (k1_tarski @ X1) @ 
% 0.62/0.82              (k4_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k1_xboole_0)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['4', '51'])).
% 0.62/0.82  thf('53', plain,
% 0.62/0.82      (![X15 : $i, X16 : $i]:
% 0.62/0.82         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.62/0.82           = (k3_xboole_0 @ X15 @ X16))),
% 0.62/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.82  thf('54', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((r2_hidden @ X1 @ X0)
% 0.62/0.82          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['52', '53'])).
% 0.62/0.82  thf('55', plain,
% 0.62/0.82      (![X12 : $i, X13 : $i]:
% 0.62/0.82         ((k4_xboole_0 @ X12 @ X13)
% 0.62/0.82           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.82  thf('56', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.62/0.82            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 0.62/0.82          | (r2_hidden @ X1 @ X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['54', '55'])).
% 0.62/0.82  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['47', '48'])).
% 0.62/0.82  thf('58', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.62/0.82          | (r2_hidden @ X1 @ X0))),
% 0.62/0.82      inference('demod', [status(thm)], ['56', '57'])).
% 0.62/0.82  thf(t69_zfmisc_1, conjecture,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.62/0.82       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.62/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.82    (~( ![A:$i,B:$i]:
% 0.62/0.82        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.62/0.82          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.62/0.82    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.62/0.82  thf('59', plain,
% 0.62/0.82      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('60', plain,
% 0.62/0.82      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.62/0.82      inference('sup-', [status(thm)], ['58', '59'])).
% 0.62/0.82  thf('61', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.62/0.82      inference('simplify', [status(thm)], ['60'])).
% 0.62/0.82  thf('62', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.62/0.82          | ~ (r2_hidden @ X0 @ X1))),
% 0.62/0.82      inference('simplify', [status(thm)], ['50'])).
% 0.62/0.82  thf('63', plain,
% 0.62/0.82      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.62/0.82      inference('sup-', [status(thm)], ['61', '62'])).
% 0.62/0.82  thf('64', plain,
% 0.62/0.82      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('65', plain, ($false),
% 0.62/0.82      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.62/0.82  
% 0.62/0.82  % SZS output end Refutation
% 0.62/0.82  
% 0.67/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
