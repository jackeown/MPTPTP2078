%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nIabDwtAGM

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:09 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 214 expanded)
%              Number of leaves         :   23 (  72 expanded)
%              Depth                    :   22
%              Number of atoms          :  604 (1581 expanded)
%              Number of equality atoms :   48 ( 137 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['3','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','16'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('34',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['45','57'])).

thf('59',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('62',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41 = X40 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('63',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nIabDwtAGM
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:34:18 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 442 iterations in 0.166s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(d3_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (![X3 : $i, X5 : $i]:
% 0.37/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf(t13_zfmisc_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.61         ( k1_tarski @ A ) ) =>
% 0.37/0.61       ( ( A ) = ( B ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i]:
% 0.37/0.61        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.61            ( k1_tarski @ A ) ) =>
% 0.37/0.61          ( ( A ) = ( B ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.37/0.61         = (k1_tarski @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t98_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X28 @ X29)
% 0.37/0.61           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X3 : $i, X5 : $i]:
% 0.37/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf(d10_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('5', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.37/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.61  thf(t28_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf(t100_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X15 : $i, X16 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X15 @ X16)
% 0.37/0.61           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf(d5_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.61       ( ![D:$i]:
% 0.37/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.61           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X10 @ X9)
% 0.37/0.61          | (r2_hidden @ X10 @ X7)
% 0.37/0.61          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.61         ((r2_hidden @ X10 @ X7)
% 0.37/0.61          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['9', '11'])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X10 @ X9)
% 0.37/0.61          | ~ (r2_hidden @ X10 @ X8)
% 0.37/0.61          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X10 @ X8)
% 0.37/0.61          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.37/0.61          | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['13', '15'])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('clc', [status(thm)], ['12', '16'])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.37/0.61      inference('sup-', [status(thm)], ['3', '17'])).
% 0.37/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.61  thf('19', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X12 : $i, X14 : $i]:
% 0.37/0.61         (((X12) = (X14))
% 0.37/0.61          | ~ (r1_tarski @ X14 @ X12)
% 0.37/0.61          | ~ (r1_tarski @ X12 @ X14))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['18', '21'])).
% 0.37/0.61  thf(t5_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.61  thf('23', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.37/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.61  thf(t91_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.61       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 0.37/0.61           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('clc', [status(thm)], ['12', '16'])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ~ (r2_hidden @ X2 @ 
% 0.37/0.61            (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ~ (r2_hidden @ X2 @ 
% 0.37/0.61            (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['24', '27'])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 0.37/0.61           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ~ (r2_hidden @ X2 @ 
% 0.37/0.61            (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ~ (r2_hidden @ X2 @ 
% 0.37/0.61            (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.37/0.61             (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['2', '30'])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ~ (r2_hidden @ X0 @ 
% 0.37/0.61            (k5_xboole_0 @ 
% 0.37/0.61             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.37/0.61             (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '31'])).
% 0.37/0.61  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['18', '21'])).
% 0.37/0.61  thf('34', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.37/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ~ (r2_hidden @ X0 @ 
% 0.37/0.61            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.37/0.61  thf('36', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (r1_tarski @ 
% 0.37/0.61          (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '35'])).
% 0.37/0.61  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['18', '21'])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['36', '39'])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      (![X3 : $i, X5 : $i]:
% 0.37/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X6 @ X7)
% 0.37/0.61          | (r2_hidden @ X6 @ X8)
% 0.37/0.61          | (r2_hidden @ X6 @ X9)
% 0.37/0.61          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.61         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.37/0.61          | (r2_hidden @ X6 @ X8)
% 0.37/0.61          | ~ (r2_hidden @ X6 @ X7))),
% 0.37/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((r1_tarski @ X0 @ X1)
% 0.37/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.37/0.61          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['41', '43'])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ k1_xboole_0)
% 0.37/0.61          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ (k1_tarski @ sk_A))
% 0.37/0.61          | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['40', '44'])).
% 0.37/0.61  thf('46', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['48', '49'])).
% 0.37/0.61  thf('51', plain,
% 0.37/0.61      (![X15 : $i, X16 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X15 @ X16)
% 0.37/0.61           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['50', '51'])).
% 0.37/0.61  thf('53', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.37/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.61  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X10 @ X8)
% 0.37/0.61          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('57', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.61      inference('condensation', [status(thm)], ['56'])).
% 0.37/0.61  thf('58', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.37/0.61          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ (k1_tarski @ sk_A)))),
% 0.37/0.61      inference('clc', [status(thm)], ['45', '57'])).
% 0.37/0.61  thf('59', plain,
% 0.37/0.61      (![X3 : $i, X5 : $i]:
% 0.37/0.61         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf('60', plain,
% 0.37/0.61      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.37/0.61        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.61  thf('61', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.37/0.61      inference('simplify', [status(thm)], ['60'])).
% 0.37/0.61  thf(t6_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.37/0.61       ( ( A ) = ( B ) ) ))).
% 0.37/0.61  thf('62', plain,
% 0.37/0.61      (![X40 : $i, X41 : $i]:
% 0.37/0.61         (((X41) = (X40))
% 0.37/0.61          | ~ (r1_tarski @ (k1_tarski @ X41) @ (k1_tarski @ X40)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.37/0.61  thf('63', plain, (((sk_B) = (sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.61  thf('64', plain, (((sk_A) != (sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('65', plain, ($false),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
