%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5y1ROE82G9

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:46 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 316 expanded)
%              Number of leaves         :   38 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  841 (2322 expanded)
%              Number of equality atoms :   79 ( 272 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ X59 )
      | ( r2_hidden @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('6',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r2_hidden @ X50 @ X48 )
      | ( r2_hidden @ X50 @ X51 )
      | ( X51
       != ( k3_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('7',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X50 @ ( k3_tarski @ X49 ) )
      | ~ ( r2_hidden @ X50 @ X48 )
      | ~ ( r2_hidden @ X48 @ X49 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('10',plain,(
    ! [X57: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X57 ) )
      = X57 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['19','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['16','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['40','41','55','60'])).

thf('62',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('63',plain,(
    ! [X61: $i] :
      ( ( k2_subset_1 @ X61 )
      = X61 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('70',plain,(
    ! [X64: $i,X65: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X64 @ X65 ) @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('71',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('73',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k2_xboole_0 @ X67 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('79',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5y1ROE82G9
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 667 iterations in 0.429s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.67/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.88  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.67/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.67/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.67/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.88  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(t25_subset_1, conjecture,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.88       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.67/0.88         ( k2_subset_1 @ A ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i,B:$i]:
% 0.67/0.88        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.88          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.67/0.88            ( k2_subset_1 @ A ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.67/0.88  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(d2_subset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( v1_xboole_0 @ A ) =>
% 0.67/0.88         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.67/0.88       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.67/0.88         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.88  thf('1', plain,
% 0.67/0.88      (![X58 : $i, X59 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X58 @ X59)
% 0.67/0.88          | (r2_hidden @ X58 @ X59)
% 0.67/0.88          | (v1_xboole_0 @ X59))),
% 0.67/0.88      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.67/0.88  thf('2', plain,
% 0.67/0.88      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.67/0.88        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.67/0.88  thf(fc1_subset_1, axiom,
% 0.67/0.88    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.67/0.88  thf('3', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 0.67/0.88      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.67/0.88  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['2', '3'])).
% 0.67/0.88  thf(d3_tarski, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.67/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.67/0.88  thf('5', plain,
% 0.67/0.88      (![X3 : $i, X5 : $i]:
% 0.67/0.88         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.88  thf(d4_tarski, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.67/0.88       ( ![C:$i]:
% 0.67/0.88         ( ( r2_hidden @ C @ B ) <=>
% 0.67/0.88           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.67/0.88  thf('6', plain,
% 0.67/0.88      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.67/0.88         (~ (r2_hidden @ X48 @ X49)
% 0.67/0.88          | ~ (r2_hidden @ X50 @ X48)
% 0.67/0.88          | (r2_hidden @ X50 @ X51)
% 0.67/0.88          | ((X51) != (k3_tarski @ X49)))),
% 0.67/0.88      inference('cnf', [status(esa)], [d4_tarski])).
% 0.67/0.88  thf('7', plain,
% 0.67/0.88      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.67/0.88         ((r2_hidden @ X50 @ (k3_tarski @ X49))
% 0.67/0.88          | ~ (r2_hidden @ X50 @ X48)
% 0.67/0.88          | ~ (r2_hidden @ X48 @ X49))),
% 0.67/0.88      inference('simplify', [status(thm)], ['6'])).
% 0.67/0.88  thf('8', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.88         ((r1_tarski @ X0 @ X1)
% 0.67/0.88          | ~ (r2_hidden @ X0 @ X2)
% 0.67/0.88          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['5', '7'])).
% 0.67/0.88  thf('9', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))
% 0.67/0.88          | (r1_tarski @ sk_B @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['4', '8'])).
% 0.67/0.88  thf(t99_zfmisc_1, axiom,
% 0.67/0.88    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.67/0.88  thf('10', plain, (![X57 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X57)) = (X57))),
% 0.67/0.88      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.67/0.88  thf('11', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A) | (r1_tarski @ sk_B @ X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.88  thf('12', plain,
% 0.67/0.88      (![X3 : $i, X5 : $i]:
% 0.67/0.88         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.88  thf('13', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.67/0.88  thf('14', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.67/0.88      inference('simplify', [status(thm)], ['13'])).
% 0.67/0.88  thf(t28_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.88  thf('15', plain,
% 0.67/0.88      (![X8 : $i, X9 : $i]:
% 0.67/0.88         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.67/0.88      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.67/0.88  thf('16', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.67/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.67/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.67/0.88  thf('17', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.88  thf(t100_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.88  thf('18', plain,
% 0.67/0.88      (![X6 : $i, X7 : $i]:
% 0.67/0.88         ((k4_xboole_0 @ X6 @ X7)
% 0.67/0.88           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.88  thf('19', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((k4_xboole_0 @ X0 @ X1)
% 0.67/0.88           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.67/0.88      inference('sup+', [status(thm)], ['17', '18'])).
% 0.67/0.88  thf(t91_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.67/0.88       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.67/0.88  thf('20', plain,
% 0.67/0.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.67/0.88           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.88  thf(t92_xboole_1, axiom,
% 0.67/0.88    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.67/0.88  thf('21', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.67/0.88  thf('22', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.67/0.88           = (k1_xboole_0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf('23', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.67/0.88  thf('24', plain,
% 0.67/0.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.67/0.88           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.88  thf('25', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.67/0.88           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.67/0.88      inference('sup+', [status(thm)], ['23', '24'])).
% 0.67/0.88  thf('26', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.67/0.88  thf('27', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.67/0.88           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.67/0.88      inference('sup+', [status(thm)], ['23', '24'])).
% 0.67/0.88  thf('28', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['26', '27'])).
% 0.67/0.88  thf(t5_boole, axiom,
% 0.67/0.88    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.88  thf('29', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.67/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.67/0.88  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['28', '29'])).
% 0.67/0.88  thf('31', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.67/0.88      inference('demod', [status(thm)], ['25', '30'])).
% 0.67/0.88  thf('32', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.67/0.88           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['22', '31'])).
% 0.67/0.88  thf('33', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.67/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.67/0.88  thf('34', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.67/0.88      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.88  thf('35', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.67/0.88           = (X1))),
% 0.67/0.88      inference('sup+', [status(thm)], ['19', '34'])).
% 0.67/0.88  thf('36', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.67/0.88      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.89  thf('37', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.67/0.89      inference('demod', [status(thm)], ['25', '30'])).
% 0.67/0.89  thf('38', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.67/0.89      inference('sup+', [status(thm)], ['36', '37'])).
% 0.67/0.89  thf('39', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.67/0.89           = (X1))),
% 0.67/0.89      inference('demod', [status(thm)], ['35', '38'])).
% 0.67/0.89  thf('40', plain,
% 0.67/0.89      (((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) = (sk_A))),
% 0.67/0.89      inference('sup+', [status(thm)], ['16', '39'])).
% 0.67/0.89  thf('41', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.67/0.89      inference('sup+', [status(thm)], ['36', '37'])).
% 0.67/0.89  thf('42', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.67/0.89      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.89  thf(t94_xboole_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( k2_xboole_0 @ A @ B ) =
% 0.67/0.89       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.89  thf('43', plain,
% 0.67/0.89      (![X17 : $i, X18 : $i]:
% 0.67/0.89         ((k2_xboole_0 @ X17 @ X18)
% 0.67/0.89           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.67/0.89              (k3_xboole_0 @ X17 @ X18)))),
% 0.67/0.89      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.67/0.89  thf('44', plain,
% 0.67/0.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.67/0.89           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.67/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.89  thf('45', plain,
% 0.67/0.89      (![X17 : $i, X18 : $i]:
% 0.67/0.89         ((k2_xboole_0 @ X17 @ X18)
% 0.67/0.89           = (k5_xboole_0 @ X17 @ 
% 0.67/0.89              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.67/0.89      inference('demod', [status(thm)], ['43', '44'])).
% 0.67/0.89  thf('46', plain,
% 0.67/0.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.67/0.89           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.67/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.89  thf('47', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.67/0.89           = (k5_xboole_0 @ X1 @ 
% 0.67/0.89              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.67/0.89      inference('sup+', [status(thm)], ['45', '46'])).
% 0.67/0.89  thf('48', plain,
% 0.67/0.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.67/0.89           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.67/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.89  thf('49', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.67/0.89           = (k5_xboole_0 @ X1 @ 
% 0.67/0.89              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))))),
% 0.67/0.89      inference('demod', [status(thm)], ['47', '48'])).
% 0.67/0.89  thf('50', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.67/0.89           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.67/0.89      inference('sup+', [status(thm)], ['42', '49'])).
% 0.67/0.89  thf('51', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.67/0.89      inference('sup+', [status(thm)], ['36', '37'])).
% 0.67/0.89  thf('52', plain,
% 0.67/0.89      (![X6 : $i, X7 : $i]:
% 0.67/0.89         ((k4_xboole_0 @ X6 @ X7)
% 0.67/0.89           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.67/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.89  thf('53', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.67/0.89           = (k4_xboole_0 @ X1 @ X0))),
% 0.67/0.89      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.67/0.89  thf('54', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.67/0.89      inference('demod', [status(thm)], ['25', '30'])).
% 0.67/0.89  thf('55', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((k2_xboole_0 @ X1 @ X0)
% 0.67/0.89           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.89      inference('sup+', [status(thm)], ['53', '54'])).
% 0.67/0.89  thf(commutativity_k2_tarski, axiom,
% 0.67/0.89    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.67/0.89  thf('56', plain,
% 0.67/0.89      (![X19 : $i, X20 : $i]:
% 0.67/0.89         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.67/0.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.67/0.89  thf(l51_zfmisc_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.67/0.89  thf('57', plain,
% 0.67/0.89      (![X55 : $i, X56 : $i]:
% 0.67/0.89         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.67/0.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.67/0.89  thf('58', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.89      inference('sup+', [status(thm)], ['56', '57'])).
% 0.67/0.89  thf('59', plain,
% 0.67/0.89      (![X55 : $i, X56 : $i]:
% 0.67/0.89         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.67/0.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.67/0.89  thf('60', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.89      inference('sup+', [status(thm)], ['58', '59'])).
% 0.67/0.89  thf('61', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.67/0.89      inference('demod', [status(thm)], ['40', '41', '55', '60'])).
% 0.67/0.89  thf('62', plain,
% 0.67/0.89      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.67/0.89         != (k2_subset_1 @ sk_A))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.67/0.89  thf('63', plain, (![X61 : $i]: ((k2_subset_1 @ X61) = (X61))),
% 0.67/0.89      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.67/0.89  thf('64', plain,
% 0.67/0.89      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.67/0.89      inference('demod', [status(thm)], ['62', '63'])).
% 0.67/0.89  thf('65', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(d5_subset_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.89       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.67/0.89  thf('66', plain,
% 0.67/0.89      (![X62 : $i, X63 : $i]:
% 0.67/0.89         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 0.67/0.89          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.67/0.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.67/0.89  thf('67', plain,
% 0.67/0.89      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.89      inference('sup-', [status(thm)], ['65', '66'])).
% 0.67/0.89  thf('68', plain,
% 0.67/0.89      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.67/0.89      inference('demod', [status(thm)], ['64', '67'])).
% 0.67/0.89  thf('69', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(dt_k3_subset_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.89       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.67/0.89  thf('70', plain,
% 0.67/0.89      (![X64 : $i, X65 : $i]:
% 0.67/0.89         ((m1_subset_1 @ (k3_subset_1 @ X64 @ X65) @ (k1_zfmisc_1 @ X64))
% 0.67/0.89          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 0.67/0.89      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.67/0.89  thf('71', plain,
% 0.67/0.89      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.89      inference('sup-', [status(thm)], ['69', '70'])).
% 0.67/0.89  thf('72', plain,
% 0.67/0.89      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.89      inference('sup-', [status(thm)], ['65', '66'])).
% 0.67/0.89  thf('73', plain,
% 0.67/0.89      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.89      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.89  thf('74', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(redefinition_k4_subset_1, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i]:
% 0.67/0.89     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.67/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.67/0.89       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.67/0.89  thf('75', plain,
% 0.67/0.89      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.67/0.89         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 0.67/0.89          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 0.67/0.89          | ((k4_subset_1 @ X68 @ X67 @ X69) = (k2_xboole_0 @ X67 @ X69)))),
% 0.67/0.89      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.67/0.89  thf('76', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.67/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['74', '75'])).
% 0.67/0.89  thf('77', plain,
% 0.67/0.89      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.67/0.89         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['73', '76'])).
% 0.67/0.89  thf(t39_xboole_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.67/0.89  thf('78', plain,
% 0.67/0.89      (![X10 : $i, X11 : $i]:
% 0.67/0.89         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.67/0.89           = (k2_xboole_0 @ X10 @ X11))),
% 0.67/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.89  thf('79', plain,
% 0.67/0.89      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.67/0.89         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.67/0.89      inference('demod', [status(thm)], ['77', '78'])).
% 0.67/0.89  thf('80', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.67/0.89      inference('demod', [status(thm)], ['68', '79'])).
% 0.67/0.89  thf('81', plain, ($false),
% 0.67/0.89      inference('simplify_reflect-', [status(thm)], ['61', '80'])).
% 0.67/0.89  
% 0.67/0.89  % SZS output end Refutation
% 0.67/0.89  
% 0.67/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
