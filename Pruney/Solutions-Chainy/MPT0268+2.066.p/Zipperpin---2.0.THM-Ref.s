%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bigwvNP2x7

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:01 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 179 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   22
%              Number of atoms          :  841 (1824 expanded)
%              Number of equality atoms :   68 ( 144 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 != X47 )
      | ~ ( r2_hidden @ X45 @ ( k4_xboole_0 @ X46 @ ( k1_tarski @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X46: $i,X47: $i] :
      ~ ( r2_hidden @ X47 @ ( k4_xboole_0 @ X46 @ ( k1_tarski @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X45: $i,X46: $i,X48: $i] :
      ( ( r2_hidden @ X45 @ ( k4_xboole_0 @ X46 @ ( k1_tarski @ X48 ) ) )
      | ( X45 = X48 )
      | ~ ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ k1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('67',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','9','66'])).

thf('68',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('69',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['11','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bigwvNP2x7
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.97/4.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.97/4.23  % Solved by: fo/fo7.sh
% 3.97/4.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.97/4.23  % done 3482 iterations in 3.766s
% 3.97/4.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.97/4.23  % SZS output start Refutation
% 3.97/4.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.97/4.23  thf(sk_A_type, type, sk_A: $i).
% 3.97/4.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.97/4.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.97/4.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.97/4.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.97/4.23  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.97/4.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.97/4.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.97/4.23  thf(t65_zfmisc_1, conjecture,
% 3.97/4.23    (![A:$i,B:$i]:
% 3.97/4.23     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 3.97/4.23       ( ~( r2_hidden @ B @ A ) ) ))).
% 3.97/4.23  thf(zf_stmt_0, negated_conjecture,
% 3.97/4.23    (~( ![A:$i,B:$i]:
% 3.97/4.23        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 3.97/4.23          ( ~( r2_hidden @ B @ A ) ) ) )),
% 3.97/4.23    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 3.97/4.23  thf('0', plain,
% 3.97/4.23      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 3.97/4.23        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 3.97/4.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.23  thf('1', plain,
% 3.97/4.23      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 3.97/4.23      inference('split', [status(esa)], ['0'])).
% 3.97/4.23  thf('2', plain,
% 3.97/4.23      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 3.97/4.23       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 3.97/4.23      inference('split', [status(esa)], ['0'])).
% 3.97/4.23  thf('3', plain,
% 3.97/4.23      (((r2_hidden @ sk_B_1 @ sk_A)
% 3.97/4.23        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 3.97/4.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.23  thf('4', plain,
% 3.97/4.23      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 3.97/4.23      inference('split', [status(esa)], ['3'])).
% 3.97/4.23  thf('5', plain,
% 3.97/4.23      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 3.97/4.23         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 3.97/4.23      inference('split', [status(esa)], ['0'])).
% 3.97/4.23  thf(t64_zfmisc_1, axiom,
% 3.97/4.23    (![A:$i,B:$i,C:$i]:
% 3.97/4.23     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 3.97/4.23       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 3.97/4.23  thf('6', plain,
% 3.97/4.23      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.97/4.23         (((X45) != (X47))
% 3.97/4.23          | ~ (r2_hidden @ X45 @ (k4_xboole_0 @ X46 @ (k1_tarski @ X47))))),
% 3.97/4.23      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 3.97/4.23  thf('7', plain,
% 3.97/4.23      (![X46 : $i, X47 : $i]:
% 3.97/4.23         ~ (r2_hidden @ X47 @ (k4_xboole_0 @ X46 @ (k1_tarski @ X47)))),
% 3.97/4.23      inference('simplify', [status(thm)], ['6'])).
% 3.97/4.23  thf('8', plain,
% 3.97/4.23      ((~ (r2_hidden @ sk_B_1 @ sk_A))
% 3.97/4.23         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 3.97/4.23      inference('sup-', [status(thm)], ['5', '7'])).
% 3.97/4.23  thf('9', plain,
% 3.97/4.23      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) | 
% 3.97/4.23       ~ ((r2_hidden @ sk_B_1 @ sk_A))),
% 3.97/4.23      inference('sup-', [status(thm)], ['4', '8'])).
% 3.97/4.23  thf('10', plain, (~ ((r2_hidden @ sk_B_1 @ sk_A))),
% 3.97/4.23      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 3.97/4.23  thf('11', plain, (~ (r2_hidden @ sk_B_1 @ sk_A)),
% 3.97/4.23      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 3.97/4.23  thf(d4_xboole_0, axiom,
% 3.97/4.23    (![A:$i,B:$i,C:$i]:
% 3.97/4.23     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.97/4.23       ( ![D:$i]:
% 3.97/4.23         ( ( r2_hidden @ D @ C ) <=>
% 3.97/4.23           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.97/4.23  thf('12', plain,
% 3.97/4.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.97/4.23         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 3.97/4.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.97/4.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.97/4.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.97/4.23  thf(t5_boole, axiom,
% 3.97/4.23    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.97/4.23  thf('13', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 3.97/4.23      inference('cnf', [status(esa)], [t5_boole])).
% 3.97/4.23  thf(t1_xboole_0, axiom,
% 3.97/4.23    (![A:$i,B:$i,C:$i]:
% 3.97/4.23     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 3.97/4.23       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 3.97/4.23  thf('14', plain,
% 3.97/4.23      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X7 @ X8)
% 3.97/4.23          | ~ (r2_hidden @ X7 @ X9)
% 3.97/4.23          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 3.97/4.23      inference('cnf', [status(esa)], [t1_xboole_0])).
% 3.97/4.23  thf('15', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X1 @ X0)
% 3.97/4.23          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 3.97/4.23          | ~ (r2_hidden @ X1 @ X0))),
% 3.97/4.23      inference('sup-', [status(thm)], ['13', '14'])).
% 3.97/4.23  thf('16', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 3.97/4.23      inference('simplify', [status(thm)], ['15'])).
% 3.97/4.23  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.97/4.23      inference('condensation', [status(thm)], ['16'])).
% 3.97/4.23  thf('18', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 3.97/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.97/4.23      inference('sup-', [status(thm)], ['12', '17'])).
% 3.97/4.23  thf('19', plain,
% 3.97/4.23      (![X45 : $i, X46 : $i, X48 : $i]:
% 3.97/4.23         ((r2_hidden @ X45 @ (k4_xboole_0 @ X46 @ (k1_tarski @ X48)))
% 3.97/4.23          | ((X45) = (X48))
% 3.97/4.23          | ~ (r2_hidden @ X45 @ X46))),
% 3.97/4.23      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 3.97/4.23  thf('20', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.23         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1))
% 3.97/4.23          | ((sk_D @ k1_xboole_0 @ X1 @ X0) = (X2))
% 3.97/4.23          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ 
% 3.97/4.23             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 3.97/4.23      inference('sup-', [status(thm)], ['18', '19'])).
% 3.97/4.23  thf('21', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 3.97/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.97/4.23      inference('sup-', [status(thm)], ['12', '17'])).
% 3.97/4.23  thf('22', plain,
% 3.97/4.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.97/4.23         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 3.97/4.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 3.97/4.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.97/4.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.97/4.23  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.97/4.23      inference('condensation', [status(thm)], ['16'])).
% 3.97/4.23  thf('24', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 3.97/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.97/4.23      inference('sup-', [status(thm)], ['22', '23'])).
% 3.97/4.23  thf('25', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X0 @ X1)
% 3.97/4.23          | ~ (r2_hidden @ X0 @ X2)
% 3.97/4.23          | (r2_hidden @ X0 @ X3)
% 3.97/4.23          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 3.97/4.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.97/4.23  thf('26', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.23         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 3.97/4.23          | ~ (r2_hidden @ X0 @ X2)
% 3.97/4.23          | ~ (r2_hidden @ X0 @ X1))),
% 3.97/4.23      inference('simplify', [status(thm)], ['25'])).
% 3.97/4.23  thf('27', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.23         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ X2)
% 3.97/4.23          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ 
% 3.97/4.23             (k3_xboole_0 @ X2 @ X0)))),
% 3.97/4.23      inference('sup-', [status(thm)], ['24', '26'])).
% 3.97/4.23  thf('28', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1))
% 3.97/4.23          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ 
% 3.97/4.23             (k3_xboole_0 @ X0 @ X1))
% 3.97/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.97/4.23      inference('sup-', [status(thm)], ['21', '27'])).
% 3.97/4.23  thf('29', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 3.97/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.97/4.23      inference('simplify', [status(thm)], ['28'])).
% 3.97/4.23  thf('30', plain,
% 3.97/4.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.97/4.23         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 3.97/4.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 3.97/4.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.97/4.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.97/4.23  thf('31', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.97/4.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('eq_fact', [status(thm)], ['30'])).
% 3.97/4.23  thf('32', plain,
% 3.97/4.23      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X4 @ X3)
% 3.97/4.23          | (r2_hidden @ X4 @ X1)
% 3.97/4.23          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 3.97/4.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.97/4.23  thf('33', plain,
% 3.97/4.23      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.97/4.23         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 3.97/4.23      inference('simplify', [status(thm)], ['32'])).
% 3.97/4.23  thf('34', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.23         (((k3_xboole_0 @ X1 @ X0)
% 3.97/4.23            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 3.97/4.23          | (r2_hidden @ 
% 3.97/4.23             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 3.97/4.23             X1))),
% 3.97/4.23      inference('sup-', [status(thm)], ['31', '33'])).
% 3.97/4.23  thf('35', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.97/4.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('eq_fact', [status(thm)], ['30'])).
% 3.97/4.23  thf('36', plain,
% 3.97/4.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.97/4.23         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.97/4.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.97/4.23  thf('37', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 3.97/4.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('sup-', [status(thm)], ['35', '36'])).
% 3.97/4.23  thf('38', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.97/4.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('simplify', [status(thm)], ['37'])).
% 3.97/4.23  thf('39', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.97/4.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('eq_fact', [status(thm)], ['30'])).
% 3.97/4.23  thf('40', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 3.97/4.23      inference('clc', [status(thm)], ['38', '39'])).
% 3.97/4.23  thf('41', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (((k3_xboole_0 @ X0 @ X1)
% 3.97/4.23            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 3.97/4.23          | ((k3_xboole_0 @ X0 @ X1)
% 3.97/4.23              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 3.97/4.23      inference('sup-', [status(thm)], ['34', '40'])).
% 3.97/4.23  thf('42', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((k3_xboole_0 @ X0 @ X1)
% 3.97/4.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.97/4.23      inference('simplify', [status(thm)], ['41'])).
% 3.97/4.23  thf(t100_xboole_1, axiom,
% 3.97/4.23    (![A:$i,B:$i]:
% 3.97/4.23     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.97/4.23  thf('43', plain,
% 3.97/4.23      (![X12 : $i, X13 : $i]:
% 3.97/4.23         ((k4_xboole_0 @ X12 @ X13)
% 3.97/4.23           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 3.97/4.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.97/4.23  thf('44', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.97/4.23           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('sup+', [status(thm)], ['42', '43'])).
% 3.97/4.23  thf('45', plain,
% 3.97/4.23      (![X12 : $i, X13 : $i]:
% 3.97/4.23         ((k4_xboole_0 @ X12 @ X13)
% 3.97/4.23           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 3.97/4.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.97/4.23  thf('46', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.97/4.23           = (k4_xboole_0 @ X1 @ X0))),
% 3.97/4.23      inference('demod', [status(thm)], ['44', '45'])).
% 3.97/4.23  thf('47', plain,
% 3.97/4.23      (![X12 : $i, X13 : $i]:
% 3.97/4.23         ((k4_xboole_0 @ X12 @ X13)
% 3.97/4.23           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 3.97/4.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.97/4.23  thf('48', plain,
% 3.97/4.23      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X7 @ X8)
% 3.97/4.23          | ~ (r2_hidden @ X7 @ X9)
% 3.97/4.23          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 3.97/4.23      inference('cnf', [status(esa)], [t1_xboole_0])).
% 3.97/4.23  thf('49', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ X2 @ X1))),
% 3.97/4.23      inference('sup-', [status(thm)], ['47', '48'])).
% 3.97/4.23  thf('50', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ X2 @ X1)
% 3.97/4.23          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.97/4.23      inference('sup-', [status(thm)], ['46', '49'])).
% 3.97/4.23  thf('51', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((k3_xboole_0 @ X0 @ X1)
% 3.97/4.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.97/4.23      inference('simplify', [status(thm)], ['41'])).
% 3.97/4.23  thf('52', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ X2 @ X1)
% 3.97/4.23          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('demod', [status(thm)], ['50', '51'])).
% 3.97/4.23  thf('53', plain,
% 3.97/4.23      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.97/4.23         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 3.97/4.23      inference('simplify', [status(thm)], ['32'])).
% 3.97/4.23  thf('54', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.23         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('clc', [status(thm)], ['52', '53'])).
% 3.97/4.23  thf('55', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0))
% 3.97/4.23          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ 
% 3.97/4.23               (k4_xboole_0 @ X1 @ X0)))),
% 3.97/4.23      inference('sup-', [status(thm)], ['29', '54'])).
% 3.97/4.23  thf('56', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (((sk_D @ k1_xboole_0 @ (k1_tarski @ X0) @ X1) = (X0))
% 3.97/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 3.97/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 3.97/4.23      inference('sup-', [status(thm)], ['20', '55'])).
% 3.97/4.23  thf('57', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 3.97/4.23          | ((sk_D @ k1_xboole_0 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 3.97/4.23      inference('simplify', [status(thm)], ['56'])).
% 3.97/4.23  thf('58', plain,
% 3.97/4.23      (![X0 : $i, X1 : $i]:
% 3.97/4.23         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 3.97/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.97/4.23      inference('sup-', [status(thm)], ['12', '17'])).
% 3.97/4.23  thf('59', plain,
% 4.06/4.23      (![X0 : $i, X1 : $i]:
% 4.06/4.23         ((r2_hidden @ X0 @ X1)
% 4.06/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 4.06/4.23          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 4.06/4.23      inference('sup+', [status(thm)], ['57', '58'])).
% 4.06/4.23  thf('60', plain,
% 4.06/4.23      (![X0 : $i, X1 : $i]:
% 4.06/4.23         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 4.06/4.23          | (r2_hidden @ X0 @ X1))),
% 4.06/4.23      inference('simplify', [status(thm)], ['59'])).
% 4.06/4.23  thf('61', plain,
% 4.06/4.23      (![X12 : $i, X13 : $i]:
% 4.06/4.23         ((k4_xboole_0 @ X12 @ X13)
% 4.06/4.23           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 4.06/4.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.06/4.23  thf('62', plain,
% 4.06/4.23      (![X0 : $i, X1 : $i]:
% 4.06/4.23         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 4.06/4.23            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 4.06/4.23          | (r2_hidden @ X0 @ X1))),
% 4.06/4.23      inference('sup+', [status(thm)], ['60', '61'])).
% 4.06/4.23  thf('63', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 4.06/4.23      inference('cnf', [status(esa)], [t5_boole])).
% 4.06/4.23  thf('64', plain,
% 4.06/4.23      (![X0 : $i, X1 : $i]:
% 4.06/4.23         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 4.06/4.23          | (r2_hidden @ X0 @ X1))),
% 4.06/4.23      inference('demod', [status(thm)], ['62', '63'])).
% 4.06/4.23  thf('65', plain,
% 4.06/4.23      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 4.06/4.23         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 4.06/4.23      inference('split', [status(esa)], ['3'])).
% 4.06/4.23  thf('66', plain,
% 4.06/4.23      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) | 
% 4.06/4.23       ((r2_hidden @ sk_B_1 @ sk_A))),
% 4.06/4.23      inference('split', [status(esa)], ['3'])).
% 4.06/4.23  thf('67', plain,
% 4.06/4.23      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 4.06/4.23      inference('sat_resolution*', [status(thm)], ['2', '9', '66'])).
% 4.06/4.23  thf('68', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A))),
% 4.06/4.23      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 4.06/4.23  thf('69', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A))),
% 4.06/4.23      inference('sup-', [status(thm)], ['64', '68'])).
% 4.06/4.23  thf('70', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 4.06/4.23      inference('simplify', [status(thm)], ['69'])).
% 4.06/4.23  thf('71', plain, ($false), inference('demod', [status(thm)], ['11', '70'])).
% 4.06/4.23  
% 4.06/4.23  % SZS output end Refutation
% 4.06/4.23  
% 4.06/4.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
