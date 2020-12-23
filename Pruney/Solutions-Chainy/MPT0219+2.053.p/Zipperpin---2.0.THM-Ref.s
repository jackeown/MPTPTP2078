%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QFBnkO6mRz

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:10 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 672 expanded)
%              Number of leaves         :   36 ( 231 expanded)
%              Depth                    :   20
%              Number of atoms          :  897 (5393 expanded)
%              Number of equality atoms :   98 ( 437 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('45',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('50',plain,(
    ! [X40: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ X42 )
      | ( X43 = X40 )
      | ( X42
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('51',plain,(
    ! [X40: $i,X43: $i] :
      ( ( X43 = X40 )
      | ~ ( r2_hidden @ X43 @ ( k1_tarski @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('57',plain,(
    ! [X45: $i] :
      ( ( k2_tarski @ X45 @ X45 )
      = ( k1_tarski @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ X38 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ X1 @ X1 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( X1 = X0 )
      | ( X1 = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_B_1 = sk_A ) ),
    inference('sup+',[status(thm)],['44','75'])).

thf('77',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X41 != X40 )
      | ( r2_hidden @ X41 @ X42 )
      | ( X42
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('80',plain,(
    ! [X40: $i] :
      ( r2_hidden @ X40 @ ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('82',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf('88',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['85','86','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QFBnkO6mRz
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 418 iterations in 0.165s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(t13_zfmisc_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.43/0.62         ( k1_tarski @ A ) ) =>
% 0.43/0.62       ( ( A ) = ( B ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i]:
% 0.43/0.62        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.43/0.62            ( k1_tarski @ A ) ) =>
% 0.43/0.62          ( ( A ) = ( B ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.43/0.62         = (k1_tarski @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t98_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X26 : $i, X27 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X26 @ X27)
% 0.43/0.62           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.43/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.43/0.62  thf('2', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.62  thf(t100_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ X15)
% 0.43/0.62           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf(t36_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.43/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.43/0.62  thf(t28_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X16 : $i, X17 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.43/0.62           = (k4_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.43/0.62           = (k4_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.43/0.62  thf(t79_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 0.43/0.62      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.62  thf(t4_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.43/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X9 @ X10)
% 0.43/0.62          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.43/0.62          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.43/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.43/0.62          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['10', '15'])).
% 0.43/0.62  thf(t7_xboole_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X13 : $i]:
% 0.43/0.62         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.43/0.62          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.43/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['16', '19'])).
% 0.43/0.62  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['9', '20'])).
% 0.43/0.62  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '21'])).
% 0.43/0.62  thf(t91_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.43/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.43/0.62           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.43/0.62  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['9', '20'])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['16', '19'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ X15)
% 0.43/0.62           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.43/0.62           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.43/0.62  thf(t5_boole, axiom,
% 0.43/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.62  thf('29', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['25', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X26 : $i, X27 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X26 @ X27)
% 0.43/0.62           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['24', '33'])).
% 0.43/0.62  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '21'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['24', '33'])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['35', '36'])).
% 0.43/0.62  thf('38', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.62  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['34', '39'])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.43/0.62           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['1', '40'])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.43/0.62         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['0', '41'])).
% 0.43/0.62  thf('43', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '21'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.43/0.62         = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.43/0.62  thf(d1_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.62       ( ![E:$i]:
% 0.43/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.43/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_1, axiom,
% 0.43/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.43/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.43/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.43/0.62          | ((X29) = (X30))
% 0.43/0.62          | ((X29) = (X31))
% 0.43/0.62          | ((X29) = (X32)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X9 @ X10)
% 0.43/0.62          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.62  thf(d4_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.43/0.62       ( ![D:$i]:
% 0.43/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.62           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X6 @ X5)
% 0.43/0.62          | (r2_hidden @ X6 @ X4)
% 0.43/0.62          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.43/0.62         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['46', '48'])).
% 0.43/0.62  thf(d1_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X40 : $i, X42 : $i, X43 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X43 @ X42)
% 0.43/0.62          | ((X43) = (X40))
% 0.43/0.62          | ((X42) != (k1_tarski @ X40)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (![X40 : $i, X43 : $i]:
% 0.43/0.62         (((X43) = (X40)) | ~ (r2_hidden @ X43 @ (k1_tarski @ X40)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.43/0.62          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['49', '51'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X9 @ X10)
% 0.43/0.62          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X6 @ X5)
% 0.43/0.62          | (r2_hidden @ X6 @ X3)
% 0.43/0.62          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.43/0.62         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['54'])).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['53', '55'])).
% 0.43/0.62  thf(t69_enumset1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      (![X45 : $i]: ((k2_tarski @ X45 @ X45) = (k1_tarski @ X45))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.62  thf(t70_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      (![X46 : $i, X47 : $i]:
% 0.43/0.62         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 0.43/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.62  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_3, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.62       ( ![E:$i]:
% 0.43/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.43/0.62  thf('59', plain,
% 0.43/0.62      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X38 @ X37)
% 0.43/0.62          | ~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 0.43/0.62          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('60', plain,
% 0.43/0.62      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 0.43/0.62         (~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 0.43/0.62          | ~ (r2_hidden @ X38 @ (k1_enumset1 @ X36 @ X35 @ X34)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['59'])).
% 0.43/0.62  thf('61', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.43/0.62          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['58', '60'])).
% 0.43/0.62  thf('62', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.43/0.62          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['57', '61'])).
% 0.43/0.62  thf('63', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.43/0.62          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['56', '62'])).
% 0.43/0.62  thf('64', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (zip_tseitin_0 @ X0 @ X1 @ X1 @ X1)
% 0.43/0.62          | (r1_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.43/0.62          | (r1_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['52', '63'])).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.43/0.62          | ~ (zip_tseitin_0 @ X0 @ X1 @ X1 @ X1))),
% 0.43/0.62      inference('simplify', [status(thm)], ['64'])).
% 0.43/0.62  thf('66', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((X1) = (X0))
% 0.43/0.62          | ((X1) = (X0))
% 0.43/0.62          | ((X1) = (X0))
% 0.43/0.62          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['45', '65'])).
% 0.43/0.62  thf('67', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X1) = (X0)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['66'])).
% 0.43/0.62  thf('68', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('69', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((X0) = (X1))
% 0.43/0.62          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.43/0.62              = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.43/0.62  thf('70', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.62  thf('71', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ X15)
% 0.43/0.62           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.62  thf('72', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.43/0.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['70', '71'])).
% 0.43/0.62  thf('73', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.43/0.62            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.43/0.62          | ((X0) = (X1)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['69', '72'])).
% 0.43/0.62  thf('74', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.62  thf('75', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.43/0.62            = (k1_tarski @ X0))
% 0.43/0.62          | ((X0) = (X1)))),
% 0.43/0.62      inference('demod', [status(thm)], ['73', '74'])).
% 0.43/0.62  thf('76', plain,
% 0.43/0.62      ((((k1_xboole_0) = (k1_tarski @ sk_B_1)) | ((sk_B_1) = (sk_A)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['44', '75'])).
% 0.43/0.62  thf('77', plain, (((sk_A) != (sk_B_1))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('78', plain, (((k1_xboole_0) = (k1_tarski @ sk_B_1))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.43/0.62  thf('79', plain,
% 0.43/0.62      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.43/0.62         (((X41) != (X40))
% 0.43/0.62          | (r2_hidden @ X41 @ X42)
% 0.43/0.62          | ((X42) != (k1_tarski @ X40)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.62  thf('80', plain, (![X40 : $i]: (r2_hidden @ X40 @ (k1_tarski @ X40))),
% 0.43/0.62      inference('simplify', [status(thm)], ['79'])).
% 0.43/0.62  thf('81', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.62  thf('82', plain,
% 0.43/0.62      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.43/0.62          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.43/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.62  thf('83', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['81', '82'])).
% 0.43/0.62  thf('84', plain,
% 0.43/0.62      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['80', '83'])).
% 0.43/0.62  thf('85', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['78', '84'])).
% 0.43/0.62  thf('86', plain, (((k1_xboole_0) = (k1_tarski @ sk_B_1))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.43/0.62  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['9', '20'])).
% 0.43/0.62  thf('88', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 0.43/0.62      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.62  thf('89', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.43/0.62      inference('sup+', [status(thm)], ['87', '88'])).
% 0.43/0.62  thf('90', plain, ($false),
% 0.43/0.62      inference('demod', [status(thm)], ['85', '86', '89'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
