%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FFBDxA3E6u

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:15 EST 2020

% Result     : Theorem 2.68s
% Output     : Refutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  226 (3494 expanded)
%              Number of leaves         :   28 (1049 expanded)
%              Depth                    :   36
%              Number of atoms          : 1911 (29510 expanded)
%              Number of equality atoms :  188 (2737 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X36 ) )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','58'])).

thf('60',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X36 ) )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
       != ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['40','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
       != ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( k1_xboole_0
       != ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ( k1_xboole_0
       != ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( k1_xboole_0
       != ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('74',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','26'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('88',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['73','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['64','90'])).

thf('92',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( X19 = X20 )
      | ( X19 = X21 )
      | ( X19 = X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('93',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('96',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('105',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['105'])).

thf('107',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('108',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('110',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['105'])).

thf('111',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['107'])).

thf('112',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('113',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('115',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('117',plain,
    ( ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['107'])).

thf('119',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['107'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','127'])).

thf('129',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('131',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X36 ) )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( k1_xboole_0
       != ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('135',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','135'])).

thf('137',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['105'])).

thf('139',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['108','137','138'])).

thf('140',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['106','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('144',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k4_xboole_0 @ X2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('148',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['107'])).

thf('149',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['108','137'])).

thf('150',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['148','149'])).

thf('151',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['146','151'])).

thf('153',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('157',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['155','160'])).

thf('162',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( sk_B
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['154','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k5_xboole_0 @ sk_B @ sk_B ) )
      | ( ( k1_tarski @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['152','167'])).

thf('169',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('171',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['168','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['141','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['106','139'])).

thf('177',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['148','149'])).

thf('180',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('182',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['140','180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('186',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('187',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('188',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['186','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['185','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['184','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['92','191'])).

thf('193',plain,(
    ! [X0: $i] : ( X0 = sk_A ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    k1_xboole_0 != sk_A ),
    inference(demod,[status(thm)],['91','193'])).

thf('195',plain,(
    ! [X0: $i] : ( X0 = sk_A ) ),
    inference(simplify,[status(thm)],['192'])).

thf('196',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['194','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FFBDxA3E6u
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:35:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 2.68/2.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.68/2.86  % Solved by: fo/fo7.sh
% 2.68/2.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.68/2.86  % done 3005 iterations in 2.387s
% 2.68/2.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.68/2.86  % SZS output start Refutation
% 2.68/2.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.68/2.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.68/2.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.68/2.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.68/2.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.68/2.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.68/2.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.68/2.86  thf(sk_B_type, type, sk_B: $i).
% 2.68/2.86  thf(sk_A_type, type, sk_A: $i).
% 2.68/2.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.68/2.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.68/2.86  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.68/2.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.68/2.86  thf(commutativity_k3_xboole_0, axiom,
% 2.68/2.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.68/2.86  thf('0', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.68/2.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.68/2.86  thf(t69_enumset1, axiom,
% 2.68/2.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.68/2.86  thf('1', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 2.68/2.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.68/2.86  thf(d5_xboole_0, axiom,
% 2.68/2.86    (![A:$i,B:$i,C:$i]:
% 2.68/2.86     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.68/2.86       ( ![D:$i]:
% 2.68/2.86         ( ( r2_hidden @ D @ C ) <=>
% 2.68/2.86           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.68/2.86  thf('2', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X7 : $i]:
% 2.68/2.86         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 2.68/2.86          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 2.68/2.86          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 2.68/2.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.68/2.86  thf(t36_xboole_1, axiom,
% 2.68/2.86    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.68/2.86  thf('3', plain,
% 2.68/2.86      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 2.68/2.86      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.68/2.86  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.68/2.86  thf('4', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 2.68/2.86      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.68/2.86  thf(d10_xboole_0, axiom,
% 2.68/2.86    (![A:$i,B:$i]:
% 2.68/2.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.68/2.86  thf('5', plain,
% 2.68/2.86      (![X8 : $i, X10 : $i]:
% 2.68/2.86         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 2.68/2.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.68/2.86  thf('6', plain,
% 2.68/2.86      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['4', '5'])).
% 2.68/2.86  thf('7', plain,
% 2.68/2.86      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['3', '6'])).
% 2.68/2.86  thf('8', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 2.68/2.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.68/2.86  thf(t65_zfmisc_1, axiom,
% 2.68/2.86    (![A:$i,B:$i]:
% 2.68/2.86     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.68/2.86       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.68/2.86  thf('9', plain,
% 2.68/2.86      (![X36 : $i, X37 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X36 @ X37)
% 2.68/2.86          | ((k4_xboole_0 @ X37 @ (k1_tarski @ X36)) != (X37)))),
% 2.68/2.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.68/2.86  thf('10', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (X1))
% 2.68/2.86          | ~ (r2_hidden @ X0 @ X1))),
% 2.68/2.86      inference('sup-', [status(thm)], ['8', '9'])).
% 2.68/2.86  thf('11', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['7', '10'])).
% 2.68/2.86  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.68/2.86      inference('simplify', [status(thm)], ['11'])).
% 2.68/2.86  thf('13', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.68/2.86          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['2', '12'])).
% 2.68/2.86  thf('14', plain,
% 2.68/2.86      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['3', '6'])).
% 2.68/2.86  thf('15', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.68/2.86          | ((X1) = (k1_xboole_0)))),
% 2.68/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.68/2.86  thf('16', plain,
% 2.68/2.86      (![X37 : $i, X38 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 2.68/2.86          | (r2_hidden @ X38 @ X37))),
% 2.68/2.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.68/2.86  thf(t48_xboole_1, axiom,
% 2.68/2.86    (![A:$i,B:$i]:
% 2.68/2.86     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.68/2.86  thf('17', plain,
% 2.68/2.86      (![X16 : $i, X17 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.68/2.86           = (k3_xboole_0 @ X16 @ X17))),
% 2.68/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.68/2.86  thf('18', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['16', '17'])).
% 2.68/2.86  thf('19', plain,
% 2.68/2.86      (![X16 : $i, X17 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.68/2.86           = (k3_xboole_0 @ X16 @ X17))),
% 2.68/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.68/2.86  thf('20', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X6 @ X5)
% 2.68/2.86          | (r2_hidden @ X6 @ X3)
% 2.68/2.86          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.68/2.86  thf('21', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.68/2.86         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['20'])).
% 2.68/2.86  thf('22', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.68/2.86      inference('sup-', [status(thm)], ['19', '21'])).
% 2.68/2.86  thf('23', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 2.68/2.86          | (r2_hidden @ X1 @ X0)
% 2.68/2.86          | (r2_hidden @ X2 @ X0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['18', '22'])).
% 2.68/2.86  thf('24', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('condensation', [status(thm)], ['23'])).
% 2.68/2.86  thf('25', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X6 @ X5)
% 2.68/2.86          | ~ (r2_hidden @ X6 @ X4)
% 2.68/2.86          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.68/2.86  thf('26', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X6 @ X4)
% 2.68/2.86          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['25'])).
% 2.68/2.86  thf('27', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 2.68/2.86      inference('clc', [status(thm)], ['24', '26'])).
% 2.68/2.86  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['15', '27'])).
% 2.68/2.86  thf('29', plain,
% 2.68/2.86      (![X16 : $i, X17 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.68/2.86           = (k3_xboole_0 @ X16 @ X17))),
% 2.68/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.68/2.86  thf('30', plain,
% 2.68/2.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['28', '29'])).
% 2.68/2.86  thf('31', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.68/2.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.68/2.86  thf('32', plain,
% 2.68/2.86      (![X16 : $i, X17 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.68/2.86           = (k3_xboole_0 @ X16 @ X17))),
% 2.68/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.68/2.86  thf('33', plain,
% 2.68/2.86      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 2.68/2.86      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.68/2.86  thf('34', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.68/2.86      inference('sup+', [status(thm)], ['32', '33'])).
% 2.68/2.86  thf('35', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.68/2.86      inference('sup+', [status(thm)], ['31', '34'])).
% 2.68/2.86  thf('36', plain,
% 2.68/2.86      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['4', '5'])).
% 2.68/2.86  thf('37', plain,
% 2.68/2.86      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['35', '36'])).
% 2.68/2.86  thf(t100_xboole_1, axiom,
% 2.68/2.86    (![A:$i,B:$i]:
% 2.68/2.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.68/2.86  thf('38', plain,
% 2.68/2.86      (![X11 : $i, X12 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X11 @ X12)
% 2.68/2.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.68/2.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.68/2.86  thf('39', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['37', '38'])).
% 2.68/2.86  thf('40', plain,
% 2.68/2.86      (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.68/2.86      inference('demod', [status(thm)], ['30', '39'])).
% 2.68/2.86  thf('41', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.68/2.86          | ((X1) = (k1_xboole_0)))),
% 2.68/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.68/2.86  thf('42', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['37', '38'])).
% 2.68/2.86  thf('43', plain,
% 2.68/2.86      (![X16 : $i, X17 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.68/2.86           = (k3_xboole_0 @ X16 @ X17))),
% 2.68/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.68/2.86  thf('44', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.68/2.86           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['42', '43'])).
% 2.68/2.86  thf('45', plain,
% 2.68/2.86      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['35', '36'])).
% 2.68/2.86  thf('46', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 2.68/2.86      inference('demod', [status(thm)], ['44', '45'])).
% 2.68/2.86  thf('47', plain,
% 2.68/2.86      (![X16 : $i, X17 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.68/2.86           = (k3_xboole_0 @ X16 @ X17))),
% 2.68/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.68/2.86  thf('48', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.68/2.86           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('sup+', [status(thm)], ['46', '47'])).
% 2.68/2.86  thf('49', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['37', '38'])).
% 2.68/2.86  thf('50', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 2.68/2.86           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('demod', [status(thm)], ['48', '49'])).
% 2.68/2.86  thf('51', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.68/2.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.68/2.86  thf('52', plain,
% 2.68/2.86      (![X16 : $i, X17 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.68/2.86           = (k3_xboole_0 @ X16 @ X17))),
% 2.68/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.68/2.86  thf('53', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X6 @ X4)
% 2.68/2.86          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['25'])).
% 2.68/2.86  thf('54', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.68/2.86          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['52', '53'])).
% 2.68/2.86  thf('55', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.68/2.86          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['51', '54'])).
% 2.68/2.86  thf('56', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.68/2.86          | ~ (r2_hidden @ X1 @ 
% 2.68/2.86               (k4_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['50', '55'])).
% 2.68/2.86  thf('57', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.68/2.86         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['20'])).
% 2.68/2.86  thf('58', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ~ (r2_hidden @ X1 @ 
% 2.68/2.86            (k4_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 2.68/2.86      inference('clc', [status(thm)], ['56', '57'])).
% 2.68/2.86  thf('59', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['41', '58'])).
% 2.68/2.86  thf('60', plain,
% 2.68/2.86      (![X36 : $i, X37 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X36 @ X37)
% 2.68/2.86          | ((k4_xboole_0 @ X37 @ (k1_tarski @ X36)) != (X37)))),
% 2.68/2.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.68/2.86  thf('61', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 2.68/2.86          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['59', '60'])).
% 2.68/2.86  thf('62', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X0 @ 
% 2.68/2.86             (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 2.68/2.86          | ((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['40', '61'])).
% 2.68/2.86  thf('63', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X0 @ 
% 2.68/2.86             (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))
% 2.68/2.86          | ((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['1', '62'])).
% 2.68/2.86  thf('64', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X0 @ 
% 2.68/2.86             (k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0)))
% 2.68/2.86          | ((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['0', '63'])).
% 2.68/2.86  thf('65', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['16', '17'])).
% 2.68/2.86  thf('66', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.68/2.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.68/2.86  thf('67', plain,
% 2.68/2.86      (![X11 : $i, X12 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X11 @ X12)
% 2.68/2.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.68/2.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.68/2.86  thf('68', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ X1)
% 2.68/2.86           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.68/2.86      inference('sup+', [status(thm)], ['66', '67'])).
% 2.68/2.86  thf('69', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 2.68/2.86            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k4_xboole_0 @ X0 @ X0)))
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['65', '68'])).
% 2.68/2.86  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['15', '27'])).
% 2.68/2.86  thf('71', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 2.68/2.86          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['59', '60'])).
% 2.68/2.86  thf('72', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X1 @ 
% 2.68/2.86             (k5_xboole_0 @ (k1_tarski @ X1) @ (k4_xboole_0 @ X0 @ X0)))
% 2.68/2.86          | ((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['70', '71'])).
% 2.68/2.86  thf('73', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 2.68/2.86          | (r2_hidden @ X1 @ X0)
% 2.68/2.86          | ((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['69', '72'])).
% 2.68/2.86  thf(t70_enumset1, axiom,
% 2.68/2.86    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.68/2.86  thf('74', plain,
% 2.68/2.86      (![X31 : $i, X32 : $i]:
% 2.68/2.86         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 2.68/2.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.68/2.86  thf(d1_enumset1, axiom,
% 2.68/2.86    (![A:$i,B:$i,C:$i,D:$i]:
% 2.68/2.86     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.68/2.86       ( ![E:$i]:
% 2.68/2.86         ( ( r2_hidden @ E @ D ) <=>
% 2.68/2.86           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.68/2.86  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.68/2.86  thf(zf_stmt_1, axiom,
% 2.68/2.86    (![E:$i,C:$i,B:$i,A:$i]:
% 2.68/2.86     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.68/2.86       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.68/2.86  thf(zf_stmt_2, axiom,
% 2.68/2.86    (![A:$i,B:$i,C:$i,D:$i]:
% 2.68/2.86     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.68/2.86       ( ![E:$i]:
% 2.68/2.86         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.68/2.86  thf('75', plain,
% 2.68/2.86      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.68/2.86         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 2.68/2.86          | (r2_hidden @ X23 @ X27)
% 2.68/2.86          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 2.68/2.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.68/2.86  thf('76', plain,
% 2.68/2.86      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.68/2.86         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 2.68/2.86          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 2.68/2.86      inference('simplify', [status(thm)], ['75'])).
% 2.68/2.86  thf('77', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.68/2.86          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.68/2.86      inference('sup+', [status(thm)], ['74', '76'])).
% 2.68/2.86  thf('78', plain,
% 2.68/2.86      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.68/2.86         (((X19) != (X18)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 2.68/2.86      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.68/2.86  thf('79', plain,
% 2.68/2.86      (![X18 : $i, X20 : $i, X21 : $i]:
% 2.68/2.86         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X18)),
% 2.68/2.86      inference('simplify', [status(thm)], ['78'])).
% 2.68/2.86  thf('80', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.68/2.86      inference('sup-', [status(thm)], ['77', '79'])).
% 2.68/2.86  thf('81', plain,
% 2.68/2.86      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 2.68/2.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.68/2.86  thf('82', plain,
% 2.68/2.86      (![X37 : $i, X38 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 2.68/2.86          | (r2_hidden @ X38 @ X37))),
% 2.68/2.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.68/2.86  thf('83', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 2.68/2.86      inference('clc', [status(thm)], ['24', '26'])).
% 2.68/2.86  thf('84', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.68/2.86          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['82', '83'])).
% 2.68/2.86  thf('85', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 2.68/2.86          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['81', '84'])).
% 2.68/2.86  thf('86', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['80', '85'])).
% 2.68/2.86  thf('87', plain,
% 2.68/2.86      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ X3)
% 2.68/2.86          | (r2_hidden @ X2 @ X4)
% 2.68/2.86          | (r2_hidden @ X2 @ X5)
% 2.68/2.86          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.68/2.86  thf('88', plain,
% 2.68/2.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.68/2.86         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 2.68/2.86          | (r2_hidden @ X2 @ X4)
% 2.68/2.86          | ~ (r2_hidden @ X2 @ X3))),
% 2.68/2.86      inference('simplify', [status(thm)], ['87'])).
% 2.68/2.86  thf('89', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ X0 @ X1)
% 2.68/2.86          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['86', '88'])).
% 2.68/2.86  thf('90', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('clc', [status(thm)], ['73', '89'])).
% 2.68/2.86  thf('91', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k1_xboole_0) != (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 2.68/2.86      inference('clc', [status(thm)], ['64', '90'])).
% 2.68/2.86  thf('92', plain,
% 2.68/2.86      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 2.68/2.86         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 2.68/2.86          | ((X19) = (X20))
% 2.68/2.86          | ((X19) = (X21))
% 2.68/2.86          | ((X19) = (X22)))),
% 2.68/2.86      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.68/2.86  thf('93', plain,
% 2.68/2.86      (![X37 : $i, X38 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 2.68/2.86          | (r2_hidden @ X38 @ X37))),
% 2.68/2.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.68/2.86  thf('94', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.68/2.86          | ((X1) = (k1_xboole_0)))),
% 2.68/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.68/2.86  thf('95', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['16', '17'])).
% 2.68/2.86  thf('96', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X6 @ X4)
% 2.68/2.86          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['25'])).
% 2.68/2.86  thf('97', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.68/2.86          | (r2_hidden @ X0 @ X1)
% 2.68/2.86          | ~ (r2_hidden @ X2 @ X1))),
% 2.68/2.86      inference('sup-', [status(thm)], ['95', '96'])).
% 2.68/2.86  thf('98', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.68/2.86      inference('sup-', [status(thm)], ['19', '21'])).
% 2.68/2.86  thf('99', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         ((r2_hidden @ X0 @ X1)
% 2.68/2.86          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 2.68/2.86      inference('clc', [status(thm)], ['97', '98'])).
% 2.68/2.86  thf('100', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 2.68/2.86          | (r2_hidden @ X0 @ X1))),
% 2.68/2.86      inference('sup-', [status(thm)], ['94', '99'])).
% 2.68/2.86  thf('101', plain,
% 2.68/2.86      (![X11 : $i, X12 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X11 @ X12)
% 2.68/2.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.68/2.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.68/2.86  thf('102', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 2.68/2.86            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 2.68/2.86          | (r2_hidden @ X0 @ X1))),
% 2.68/2.86      inference('sup+', [status(thm)], ['100', '101'])).
% 2.68/2.86  thf('103', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.68/2.86          | (r2_hidden @ X1 @ X0)
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['93', '102'])).
% 2.68/2.86  thf('104', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ X1 @ X0) | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['103'])).
% 2.68/2.86  thf(t67_zfmisc_1, conjecture,
% 2.68/2.86    (![A:$i,B:$i]:
% 2.68/2.86     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 2.68/2.86       ( ~( r2_hidden @ A @ B ) ) ))).
% 2.68/2.86  thf(zf_stmt_3, negated_conjecture,
% 2.68/2.86    (~( ![A:$i,B:$i]:
% 2.68/2.86        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 2.68/2.86          ( ~( r2_hidden @ A @ B ) ) ) )),
% 2.68/2.86    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 2.68/2.86  thf('105', plain,
% 2.68/2.86      (((r2_hidden @ sk_A @ sk_B)
% 2.68/2.86        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 2.68/2.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.68/2.86  thf('106', plain,
% 2.68/2.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 2.68/2.86         <= (~
% 2.68/2.86             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('split', [status(esa)], ['105'])).
% 2.68/2.86  thf('107', plain,
% 2.68/2.86      ((~ (r2_hidden @ sk_A @ sk_B)
% 2.68/2.86        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 2.68/2.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.68/2.86  thf('108', plain,
% 2.68/2.86      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 2.68/2.86       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 2.68/2.86      inference('split', [status(esa)], ['107'])).
% 2.68/2.86  thf('109', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.68/2.86          | ((X1) = (k1_xboole_0)))),
% 2.68/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.68/2.86  thf('110', plain,
% 2.68/2.86      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.68/2.86      inference('split', [status(esa)], ['105'])).
% 2.68/2.86  thf('111', plain,
% 2.68/2.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('split', [status(esa)], ['107'])).
% 2.68/2.86  thf('112', plain,
% 2.68/2.86      (![X16 : $i, X17 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.68/2.86           = (k3_xboole_0 @ X16 @ X17))),
% 2.68/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.68/2.86  thf('113', plain,
% 2.68/2.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 2.68/2.86          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('sup+', [status(thm)], ['111', '112'])).
% 2.68/2.86  thf('114', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.68/2.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.68/2.86  thf('115', plain,
% 2.68/2.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 2.68/2.86          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('demod', [status(thm)], ['113', '114'])).
% 2.68/2.86  thf('116', plain,
% 2.68/2.86      (![X37 : $i, X38 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 2.68/2.86          | (r2_hidden @ X38 @ X37))),
% 2.68/2.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.68/2.86  thf('117', plain,
% 2.68/2.86      (((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))
% 2.68/2.86         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('sup+', [status(thm)], ['115', '116'])).
% 2.68/2.86  thf('118', plain,
% 2.68/2.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('split', [status(esa)], ['107'])).
% 2.68/2.86  thf('119', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X6 @ X4)
% 2.68/2.86          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['25'])).
% 2.68/2.86  thf('120', plain,
% 2.68/2.86      ((![X0 : $i]:
% 2.68/2.86          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('sup-', [status(thm)], ['118', '119'])).
% 2.68/2.86  thf('121', plain,
% 2.68/2.86      (((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))
% 2.68/2.86         | ~ (r2_hidden @ sk_A @ sk_B)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('sup-', [status(thm)], ['117', '120'])).
% 2.68/2.86  thf('122', plain,
% 2.68/2.86      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 2.68/2.86             ((r2_hidden @ sk_A @ sk_B)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['110', '121'])).
% 2.68/2.86  thf('123', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.68/2.86          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['51', '54'])).
% 2.68/2.86  thf('124', plain,
% 2.68/2.86      ((![X0 : $i]:
% 2.68/2.86          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.68/2.86           | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 2.68/2.86             ((r2_hidden @ sk_A @ sk_B)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['122', '123'])).
% 2.68/2.86  thf('125', plain,
% 2.68/2.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 2.68/2.86      inference('split', [status(esa)], ['107'])).
% 2.68/2.86  thf('126', plain,
% 2.68/2.86      ((![X0 : $i]:
% 2.68/2.86          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.68/2.86           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 2.68/2.86             ((r2_hidden @ sk_A @ sk_B)))),
% 2.68/2.86      inference('demod', [status(thm)], ['124', '125'])).
% 2.68/2.86  thf('127', plain,
% 2.68/2.86      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 2.68/2.86             ((r2_hidden @ sk_A @ sk_B)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['126'])).
% 2.68/2.86  thf('128', plain,
% 2.68/2.86      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 2.68/2.86             ((r2_hidden @ sk_A @ sk_B)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['109', '127'])).
% 2.68/2.86  thf('129', plain,
% 2.68/2.86      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 2.68/2.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.68/2.86  thf('130', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['15', '27'])).
% 2.68/2.86  thf('131', plain,
% 2.68/2.86      (![X36 : $i, X37 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X36 @ X37)
% 2.68/2.86          | ((k4_xboole_0 @ X37 @ (k1_tarski @ X36)) != (X37)))),
% 2.68/2.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.68/2.86  thf('132', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (((k1_xboole_0) != (k1_tarski @ X0))
% 2.68/2.86          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['130', '131'])).
% 2.68/2.86  thf('133', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 2.68/2.86          | ((k1_xboole_0) != (k1_tarski @ X0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['129', '132'])).
% 2.68/2.86  thf('134', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.68/2.86      inference('sup-', [status(thm)], ['77', '79'])).
% 2.68/2.86  thf('135', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 2.68/2.86      inference('demod', [status(thm)], ['133', '134'])).
% 2.68/2.86  thf('136', plain,
% 2.68/2.86      ((((k1_xboole_0) != (k1_xboole_0)))
% 2.68/2.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 2.68/2.86             ((r2_hidden @ sk_A @ sk_B)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['128', '135'])).
% 2.68/2.86  thf('137', plain,
% 2.68/2.86      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 2.68/2.86       ~ ((r2_hidden @ sk_A @ sk_B))),
% 2.68/2.86      inference('simplify', [status(thm)], ['136'])).
% 2.68/2.86  thf('138', plain,
% 2.68/2.86      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 2.68/2.86       ((r2_hidden @ sk_A @ sk_B))),
% 2.68/2.86      inference('split', [status(esa)], ['105'])).
% 2.68/2.86  thf('139', plain,
% 2.68/2.86      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 2.68/2.86      inference('sat_resolution*', [status(thm)], ['108', '137', '138'])).
% 2.68/2.86  thf('140', plain,
% 2.68/2.86      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 2.68/2.86      inference('simpl_trail', [status(thm)], ['106', '139'])).
% 2.68/2.86  thf('141', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['15', '27'])).
% 2.68/2.86  thf('142', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ X1 @ X0) | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['103'])).
% 2.68/2.86  thf('143', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.68/2.86          | ((X1) = (k1_xboole_0)))),
% 2.68/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.68/2.86  thf('144', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X6 @ X4)
% 2.68/2.86          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['25'])).
% 2.68/2.86  thf('145', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.68/2.86          | ~ (r2_hidden @ 
% 2.68/2.86               (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ X0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['143', '144'])).
% 2.68/2.86  thf('146', plain,
% 2.68/2.86      (![X0 : $i, X2 : $i]:
% 2.68/2.86         (((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.68/2.86          | ((k4_xboole_0 @ X2 @ X0) = (k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['142', '145'])).
% 2.68/2.86  thf('147', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ X1 @ X0) | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['103'])).
% 2.68/2.86  thf('148', plain,
% 2.68/2.86      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.68/2.86      inference('split', [status(esa)], ['107'])).
% 2.68/2.86  thf('149', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 2.68/2.86      inference('sat_resolution*', [status(thm)], ['108', '137'])).
% 2.68/2.86  thf('150', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 2.68/2.86      inference('simpl_trail', [status(thm)], ['148', '149'])).
% 2.68/2.86  thf('151', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['147', '150'])).
% 2.68/2.86  thf('152', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((sk_B) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X1 @ X0)))
% 2.68/2.86          | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('sup+', [status(thm)], ['146', '151'])).
% 2.68/2.86  thf('153', plain,
% 2.68/2.86      (![X37 : $i, X38 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 2.68/2.86          | (r2_hidden @ X38 @ X37))),
% 2.68/2.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.68/2.86  thf('154', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['80', '85'])).
% 2.68/2.86  thf('155', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((r2_hidden @ X1 @ X0) | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['103'])).
% 2.68/2.86  thf('156', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 2.68/2.86           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('demod', [status(thm)], ['48', '49'])).
% 2.68/2.86  thf('157', plain,
% 2.68/2.86      (![X11 : $i, X12 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X11 @ X12)
% 2.68/2.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.68/2.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.68/2.86  thf('158', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.68/2.86           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.68/2.86      inference('sup+', [status(thm)], ['156', '157'])).
% 2.68/2.86  thf('159', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 2.68/2.86      inference('demod', [status(thm)], ['44', '45'])).
% 2.68/2.86  thf('160', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['158', '159'])).
% 2.68/2.86  thf('161', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0)) | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['155', '160'])).
% 2.68/2.86  thf('162', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['147', '150'])).
% 2.68/2.86  thf('163', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((sk_B) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ X0)))
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['161', '162'])).
% 2.68/2.86  thf('164', plain,
% 2.68/2.86      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X6 @ X4)
% 2.68/2.86          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['25'])).
% 2.68/2.86  thf('165', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (((sk_B)
% 2.68/2.86            = (k5_xboole_0 @ sk_B @ 
% 2.68/2.86               (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))
% 2.68/2.86          | ~ (r2_hidden @ X2 @ X0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['163', '164'])).
% 2.68/2.86  thf('166', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         ((sk_B)
% 2.68/2.86           = (k5_xboole_0 @ sk_B @ 
% 2.68/2.86              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 2.68/2.86               (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))))),
% 2.68/2.86      inference('sup-', [status(thm)], ['154', '165'])).
% 2.68/2.86  thf('167', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((sk_B)
% 2.68/2.86            = (k5_xboole_0 @ sk_B @ 
% 2.68/2.86               (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))))
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['153', '166'])).
% 2.68/2.86  thf('168', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (((sk_B) = (k5_xboole_0 @ sk_B @ sk_B))
% 2.68/2.86          | ((k1_tarski @ X0) = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 2.68/2.86          | (r2_hidden @ X0 @ sk_B))),
% 2.68/2.86      inference('sup+', [status(thm)], ['152', '167'])).
% 2.68/2.86  thf('169', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['147', '150'])).
% 2.68/2.86  thf('170', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['158', '159'])).
% 2.68/2.86  thf('171', plain, (((k5_xboole_0 @ sk_B @ sk_B) = (k1_xboole_0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['169', '170'])).
% 2.68/2.86  thf('172', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (((sk_B) = (k1_xboole_0))
% 2.68/2.86          | (r2_hidden @ X0 @ sk_B)
% 2.68/2.86          | ((k1_tarski @ X0) = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 2.68/2.86      inference('sup+', [status(thm)], ['168', '171'])).
% 2.68/2.86  thf('173', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k1_tarski @ X1)
% 2.68/2.86            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k4_xboole_0 @ X0 @ X0)))
% 2.68/2.86          | (r2_hidden @ X1 @ sk_B)
% 2.68/2.86          | ((sk_B) = (k1_xboole_0)))),
% 2.68/2.86      inference('sup+', [status(thm)], ['141', '172'])).
% 2.68/2.86  thf('174', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 2.68/2.86            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k4_xboole_0 @ X0 @ X0)))
% 2.68/2.86          | (r2_hidden @ X1 @ X0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['65', '68'])).
% 2.68/2.86  thf('175', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 2.68/2.86          | ((sk_B) = (k1_xboole_0))
% 2.68/2.86          | (r2_hidden @ X0 @ sk_B)
% 2.68/2.86          | (r2_hidden @ X0 @ X1))),
% 2.68/2.86      inference('sup+', [status(thm)], ['173', '174'])).
% 2.68/2.86  thf('176', plain,
% 2.68/2.86      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 2.68/2.86      inference('simpl_trail', [status(thm)], ['106', '139'])).
% 2.68/2.86  thf('177', plain,
% 2.68/2.86      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 2.68/2.86        | (r2_hidden @ sk_A @ sk_B)
% 2.68/2.86        | (r2_hidden @ sk_A @ sk_B)
% 2.68/2.86        | ((sk_B) = (k1_xboole_0)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['175', '176'])).
% 2.68/2.86  thf('178', plain, ((((sk_B) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B))),
% 2.68/2.86      inference('simplify', [status(thm)], ['177'])).
% 2.68/2.86  thf('179', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 2.68/2.86      inference('simpl_trail', [status(thm)], ['148', '149'])).
% 2.68/2.86  thf('180', plain, (((sk_B) = (k1_xboole_0))),
% 2.68/2.86      inference('clc', [status(thm)], ['178', '179'])).
% 2.68/2.86  thf('181', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.68/2.86      inference('sup+', [status(thm)], ['37', '38'])).
% 2.68/2.86  thf('182', plain,
% 2.68/2.86      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 2.68/2.86      inference('demod', [status(thm)], ['140', '180', '181'])).
% 2.68/2.86  thf('183', plain,
% 2.68/2.86      (![X0 : $i]:
% 2.68/2.86         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 2.68/2.86          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['104', '182'])).
% 2.68/2.86  thf('184', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 2.68/2.86      inference('simplify', [status(thm)], ['183'])).
% 2.68/2.86  thf('185', plain,
% 2.68/2.86      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 2.68/2.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.68/2.86  thf('186', plain,
% 2.68/2.86      (![X31 : $i, X32 : $i]:
% 2.68/2.86         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 2.68/2.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.68/2.86  thf('187', plain,
% 2.68/2.86      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X28 @ X27)
% 2.68/2.86          | ~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 2.68/2.86          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 2.68/2.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.68/2.86  thf('188', plain,
% 2.68/2.86      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 2.68/2.86         (~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 2.68/2.86          | ~ (r2_hidden @ X28 @ (k1_enumset1 @ X26 @ X25 @ X24)))),
% 2.68/2.86      inference('simplify', [status(thm)], ['187'])).
% 2.68/2.86  thf('189', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.68/2.86          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.68/2.86      inference('sup-', [status(thm)], ['186', '188'])).
% 2.68/2.86  thf('190', plain,
% 2.68/2.86      (![X0 : $i, X1 : $i]:
% 2.68/2.86         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.68/2.86          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 2.68/2.86      inference('sup-', [status(thm)], ['185', '189'])).
% 2.68/2.86  thf('191', plain, (![X0 : $i]: ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A)),
% 2.68/2.86      inference('sup-', [status(thm)], ['184', '190'])).
% 2.68/2.86  thf('192', plain,
% 2.68/2.86      (![X0 : $i]: (((X0) = (sk_A)) | ((X0) = (sk_A)) | ((X0) = (sk_A)))),
% 2.68/2.86      inference('sup-', [status(thm)], ['92', '191'])).
% 2.68/2.86  thf('193', plain, (![X0 : $i]: ((X0) = (sk_A))),
% 2.68/2.86      inference('simplify', [status(thm)], ['192'])).
% 2.68/2.86  thf('194', plain, (((k1_xboole_0) != (sk_A))),
% 2.68/2.86      inference('demod', [status(thm)], ['91', '193'])).
% 2.68/2.86  thf('195', plain, (![X0 : $i]: ((X0) = (sk_A))),
% 2.68/2.86      inference('simplify', [status(thm)], ['192'])).
% 2.68/2.86  thf('196', plain, ($false),
% 2.68/2.86      inference('simplify_reflect+', [status(thm)], ['194', '195'])).
% 2.68/2.86  
% 2.68/2.86  % SZS output end Refutation
% 2.68/2.86  
% 2.68/2.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
