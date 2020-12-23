%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M569BA4v0p

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:14 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 402 expanded)
%              Number of leaves         :   29 ( 133 expanded)
%              Depth                    :   20
%              Number of atoms          : 1015 (3326 expanded)
%              Number of equality atoms :   72 ( 288 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( X22 = X23 )
      | ( X22 = X24 )
      | ( X22 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('19',plain,(
    ! [X63: $i] :
      ( ~ ( r2_hidden @ X63 @ sk_A )
      | ( X63 = sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_B )
      = o_0_0_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('36',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['34','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_tarski @ sk_B )
    = o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['24','43'])).

thf('45',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('55',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X1 )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('60',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('63',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('69',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','72'])).

thf('74',plain,(
    r2_hidden @ sk_B @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['44','73'])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('76',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

thf('77',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X9 ) )
      | ( r2_hidden @ X6 @ X9 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('89',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_A ) )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('91',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_A ) )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('93',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('97',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','100'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['101','106'])).

thf('108',plain,(
    $false ),
    inference('sup-',[status(thm)],['74','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M569BA4v0p
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.87  % Solved by: fo/fo7.sh
% 0.67/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.87  % done 798 iterations in 0.418s
% 0.67/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.87  % SZS output start Refutation
% 0.67/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.67/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.67/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.87  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.67/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.87  thf(d1_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.87     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.67/0.87       ( ![E:$i]:
% 0.67/0.87         ( ( r2_hidden @ E @ D ) <=>
% 0.67/0.87           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.67/0.87  thf(zf_stmt_0, axiom,
% 0.67/0.87    (![E:$i,C:$i,B:$i,A:$i]:
% 0.67/0.87     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.67/0.87       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.67/0.87  thf('0', plain,
% 0.67/0.87      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.67/0.87         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.67/0.87          | ((X22) = (X23))
% 0.67/0.87          | ((X22) = (X24))
% 0.67/0.87          | ((X22) = (X25)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(d3_tarski, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( r1_tarski @ A @ B ) <=>
% 0.67/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.67/0.87  thf('1', plain,
% 0.67/0.87      (![X3 : $i, X5 : $i]:
% 0.67/0.87         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf(t69_enumset1, axiom,
% 0.67/0.87    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.67/0.87  thf('2', plain, (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.67/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.67/0.87  thf(t70_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.67/0.87  thf('3', plain,
% 0.67/0.87      (![X34 : $i, X35 : $i]:
% 0.67/0.87         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.67/0.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.67/0.87  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.67/0.87  thf(zf_stmt_2, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.87     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.67/0.87       ( ![E:$i]:
% 0.67/0.87         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.67/0.87  thf('4', plain,
% 0.67/0.87      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X31 @ X30)
% 0.67/0.87          | ~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 0.67/0.87          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.87  thf('5', plain,
% 0.67/0.87      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.67/0.87         (~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 0.67/0.87          | ~ (r2_hidden @ X31 @ (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['4'])).
% 0.67/0.87  thf('6', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.67/0.87          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['3', '5'])).
% 0.67/0.87  thf('7', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.67/0.87          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['2', '6'])).
% 0.67/0.87  thf('8', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.67/0.87          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['1', '7'])).
% 0.67/0.87  thf('9', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.67/0.87          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.67/0.87          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.67/0.87          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['0', '8'])).
% 0.67/0.87  thf('10', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.67/0.87          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['9'])).
% 0.67/0.87  thf('11', plain,
% 0.67/0.87      (![X3 : $i, X5 : $i]:
% 0.67/0.87         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf('12', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.67/0.87          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.67/0.87          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['10', '11'])).
% 0.67/0.87  thf('13', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.67/0.87          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['12'])).
% 0.67/0.87  thf(t38_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.67/0.87       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.87  thf('14', plain,
% 0.67/0.87      (![X19 : $i, X20 : $i]:
% 0.67/0.87         (((X19) = (k1_xboole_0))
% 0.67/0.87          | ~ (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.67/0.87  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.67/0.87  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.67/0.87      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.67/0.87  thf('16', plain,
% 0.67/0.87      (![X19 : $i, X20 : $i]:
% 0.67/0.87         (((X19) = (o_0_0_xboole_0))
% 0.67/0.87          | ~ (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.67/0.87      inference('demod', [status(thm)], ['14', '15'])).
% 0.67/0.87  thf('17', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.67/0.87          | ((k1_tarski @ X0) = (o_0_0_xboole_0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['13', '16'])).
% 0.67/0.87  thf('18', plain,
% 0.67/0.87      (![X3 : $i, X5 : $i]:
% 0.67/0.87         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf(t41_zfmisc_1, conjecture,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.67/0.87          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.67/0.87  thf(zf_stmt_3, negated_conjecture,
% 0.67/0.87    (~( ![A:$i,B:$i]:
% 0.67/0.87        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.67/0.87             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.67/0.87    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.67/0.87  thf('19', plain,
% 0.67/0.87      (![X63 : $i]: (~ (r2_hidden @ X63 @ sk_A) | ((X63) = (sk_B)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.67/0.87  thf('20', plain,
% 0.67/0.87      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.87  thf('21', plain,
% 0.67/0.87      (![X3 : $i, X5 : $i]:
% 0.67/0.87         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf('22', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         (~ (r2_hidden @ sk_B @ X0)
% 0.67/0.87          | (r1_tarski @ sk_A @ X0)
% 0.67/0.87          | (r1_tarski @ sk_A @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['20', '21'])).
% 0.67/0.87  thf('23', plain,
% 0.67/0.87      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.67/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.67/0.87  thf('24', plain,
% 0.67/0.87      ((((k1_tarski @ sk_B) = (o_0_0_xboole_0))
% 0.67/0.87        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['17', '23'])).
% 0.67/0.87  thf('25', plain,
% 0.67/0.87      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.87  thf('26', plain,
% 0.67/0.87      (![X3 : $i, X5 : $i]:
% 0.67/0.87         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf('27', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((r2_hidden @ sk_B @ sk_A)
% 0.67/0.87          | (r1_tarski @ sk_A @ X0)
% 0.67/0.87          | (r1_tarski @ sk_A @ X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['25', '26'])).
% 0.67/0.87  thf('28', plain,
% 0.67/0.87      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (r2_hidden @ sk_B @ sk_A))),
% 0.67/0.87      inference('simplify', [status(thm)], ['27'])).
% 0.67/0.87  thf('29', plain,
% 0.67/0.87      (![X19 : $i, X20 : $i]:
% 0.67/0.87         (((X19) = (o_0_0_xboole_0))
% 0.67/0.87          | ~ (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.67/0.87      inference('demod', [status(thm)], ['14', '15'])).
% 0.67/0.87  thf('30', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_A) = (o_0_0_xboole_0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.87  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.67/0.87  thf('32', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.67/0.87      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.67/0.87  thf('33', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.67/0.87      inference('demod', [status(thm)], ['31', '32'])).
% 0.67/0.87  thf('34', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.67/0.87      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.67/0.87  thf('35', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.67/0.87          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['9'])).
% 0.67/0.87  thf('36', plain,
% 0.67/0.87      (![X3 : $i, X5 : $i]:
% 0.67/0.87         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf('37', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X0 @ X1)
% 0.67/0.87          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.67/0.87          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.87  thf('38', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.67/0.87      inference('simplify', [status(thm)], ['37'])).
% 0.67/0.87  thf('39', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.67/0.87      inference('sup-', [status(thm)], ['34', '38'])).
% 0.67/0.87  thf(d10_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.87  thf('40', plain,
% 0.67/0.87      (![X10 : $i, X12 : $i]:
% 0.67/0.87         (((X10) = (X12))
% 0.67/0.87          | ~ (r1_tarski @ X12 @ X10)
% 0.67/0.87          | ~ (r1_tarski @ X10 @ X12))),
% 0.67/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.87  thf('41', plain,
% 0.67/0.87      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B))
% 0.67/0.87        | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['39', '40'])).
% 0.67/0.87  thf('42', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.67/0.87  thf('43', plain, (~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.67/0.87      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.67/0.87  thf('44', plain, (((k1_tarski @ sk_B) = (o_0_0_xboole_0))),
% 0.67/0.87      inference('clc', [status(thm)], ['24', '43'])).
% 0.67/0.87  thf('45', plain,
% 0.67/0.87      (![X34 : $i, X35 : $i]:
% 0.67/0.87         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.67/0.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.67/0.87  thf('46', plain,
% 0.67/0.87      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.67/0.87         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.67/0.87          | (r2_hidden @ X26 @ X30)
% 0.67/0.87          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.87  thf('47', plain,
% 0.67/0.87      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.67/0.87         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 0.67/0.87          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 0.67/0.87      inference('simplify', [status(thm)], ['46'])).
% 0.67/0.87  thf('48', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.67/0.87          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['45', '47'])).
% 0.67/0.87  thf('49', plain,
% 0.67/0.87      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.67/0.87         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('50', plain,
% 0.67/0.87      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.67/0.87         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 0.67/0.87      inference('simplify', [status(thm)], ['49'])).
% 0.67/0.87  thf('51', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['48', '50'])).
% 0.67/0.87  thf('52', plain,
% 0.67/0.87      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.67/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.67/0.87  thf('53', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.67/0.87          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['12'])).
% 0.67/0.87  thf(t17_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.67/0.87  thf('54', plain,
% 0.67/0.87      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.67/0.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.67/0.87  thf('55', plain,
% 0.67/0.87      (![X10 : $i, X12 : $i]:
% 0.67/0.87         (((X10) = (X12))
% 0.67/0.87          | ~ (r1_tarski @ X12 @ X10)
% 0.67/0.87          | ~ (r1_tarski @ X10 @ X12))),
% 0.67/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.87  thf('56', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.67/0.87          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.87  thf('57', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r2_hidden @ X1 @ (k1_tarski @ X1))
% 0.67/0.87          | ((k1_tarski @ X1) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['53', '56'])).
% 0.67/0.87  thf(commutativity_k3_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.67/0.87  thf('58', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.87  thf(t100_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.87  thf('59', plain,
% 0.67/0.87      (![X13 : $i, X14 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X13 @ X14)
% 0.67/0.87           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.87  thf(t1_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.67/0.87       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.67/0.87  thf('60', plain,
% 0.67/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X6 @ X7)
% 0.67/0.87          | ~ (r2_hidden @ X6 @ X8)
% 0.67/0.87          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.67/0.87  thf('61', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.67/0.87          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87          | ~ (r2_hidden @ X2 @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['59', '60'])).
% 0.67/0.87  thf('62', plain,
% 0.67/0.87      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.67/0.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.67/0.87  thf('63', plain,
% 0.67/0.87      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ X3)
% 0.67/0.87          | (r2_hidden @ X2 @ X4)
% 0.67/0.87          | ~ (r1_tarski @ X3 @ X4))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf('64', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['62', '63'])).
% 0.67/0.87  thf('65', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('clc', [status(thm)], ['61', '64'])).
% 0.67/0.87  thf('66', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['58', '65'])).
% 0.67/0.87  thf('67', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.67/0.87          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.67/0.87          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['57', '66'])).
% 0.67/0.87  thf('68', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.67/0.87          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['12'])).
% 0.67/0.87  thf('69', plain,
% 0.67/0.87      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ X3)
% 0.67/0.87          | (r2_hidden @ X2 @ X4)
% 0.67/0.87          | ~ (r1_tarski @ X3 @ X4))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf('70', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         ((r2_hidden @ X1 @ (k1_tarski @ X1))
% 0.67/0.87          | (r2_hidden @ X2 @ X0)
% 0.67/0.87          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['68', '69'])).
% 0.67/0.87  thf('71', plain,
% 0.67/0.87      (![X0 : $i, X2 : $i]:
% 0.67/0.87         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.67/0.87          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0)))),
% 0.67/0.87      inference('clc', [status(thm)], ['67', '70'])).
% 0.67/0.87  thf('72', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.67/0.87          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['52', '71'])).
% 0.67/0.87  thf('73', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['51', '72'])).
% 0.67/0.87  thf('74', plain, ((r2_hidden @ sk_B @ o_0_0_xboole_0)),
% 0.67/0.87      inference('sup+', [status(thm)], ['44', '73'])).
% 0.67/0.87  thf('75', plain,
% 0.67/0.87      (![X13 : $i, X14 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X13 @ X14)
% 0.67/0.87           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.87  thf('76', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.67/0.87      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.67/0.87  thf('77', plain,
% 0.67/0.87      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.67/0.87         ((r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X9))
% 0.67/0.87          | (r2_hidden @ X6 @ X9)
% 0.67/0.87          | ~ (r2_hidden @ X6 @ X7))),
% 0.67/0.87      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.67/0.87  thf('78', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((r2_hidden @ sk_B @ X0)
% 0.67/0.87          | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['76', '77'])).
% 0.67/0.87  thf('79', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.67/0.87          | (r2_hidden @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.67/0.87      inference('sup+', [status(thm)], ['75', '78'])).
% 0.67/0.87  thf('80', plain,
% 0.67/0.87      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.67/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.67/0.87  thf('81', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.67/0.87          | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['79', '80'])).
% 0.67/0.87  thf('82', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.87  thf('83', plain,
% 0.67/0.87      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.67/0.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.67/0.87  thf('84', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.67/0.87      inference('sup+', [status(thm)], ['82', '83'])).
% 0.67/0.87  thf('85', plain,
% 0.67/0.87      (![X10 : $i, X12 : $i]:
% 0.67/0.87         (((X10) = (X12))
% 0.67/0.87          | ~ (r1_tarski @ X12 @ X10)
% 0.67/0.87          | ~ (r1_tarski @ X10 @ X12))),
% 0.67/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.87  thf('86', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.87  thf('87', plain,
% 0.67/0.87      (((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ sk_A))
% 0.67/0.87        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['81', '86'])).
% 0.67/0.87  thf('88', plain,
% 0.67/0.87      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.67/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.67/0.87  thf('89', plain,
% 0.67/0.87      ((((sk_A) = (k3_xboole_0 @ sk_A @ sk_A))
% 0.67/0.87        | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['87', '88'])).
% 0.67/0.87  thf('90', plain,
% 0.67/0.87      (![X19 : $i, X20 : $i]:
% 0.67/0.87         (((X19) = (o_0_0_xboole_0))
% 0.67/0.87          | ~ (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.67/0.87      inference('demod', [status(thm)], ['14', '15'])).
% 0.67/0.87  thf('91', plain,
% 0.67/0.87      ((((sk_A) = (k3_xboole_0 @ sk_A @ sk_A)) | ((sk_A) = (o_0_0_xboole_0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['89', '90'])).
% 0.67/0.87  thf('92', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.67/0.87      inference('demod', [status(thm)], ['31', '32'])).
% 0.67/0.87  thf('93', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_A))),
% 0.67/0.87      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.67/0.87  thf('94', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('clc', [status(thm)], ['61', '64'])).
% 0.67/0.87  thf('95', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X0 @ sk_A)
% 0.67/0.87          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['93', '94'])).
% 0.67/0.87  thf('96', plain,
% 0.67/0.87      (![X13 : $i, X14 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X13 @ X14)
% 0.67/0.87           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.87  thf('97', plain,
% 0.67/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.67/0.87         ((r2_hidden @ X6 @ X7)
% 0.67/0.87          | (r2_hidden @ X6 @ X8)
% 0.67/0.87          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.67/0.87  thf('98', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.67/0.87          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87          | (r2_hidden @ X2 @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['96', '97'])).
% 0.67/0.87  thf('99', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('clc', [status(thm)], ['61', '64'])).
% 0.67/0.87  thf('100', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         ((r2_hidden @ X2 @ X1) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('clc', [status(thm)], ['98', '99'])).
% 0.67/0.87  thf('101', plain,
% 0.67/0.87      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_A))),
% 0.67/0.87      inference('clc', [status(thm)], ['95', '100'])).
% 0.67/0.87  thf('102', plain,
% 0.67/0.87      (![X3 : $i, X5 : $i]:
% 0.67/0.87         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.67/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.87  thf('103', plain,
% 0.67/0.87      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_A))),
% 0.67/0.87      inference('clc', [status(thm)], ['95', '100'])).
% 0.67/0.87  thf('104', plain,
% 0.67/0.87      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ X0)),
% 0.67/0.87      inference('sup-', [status(thm)], ['102', '103'])).
% 0.67/0.87  thf('105', plain,
% 0.67/0.87      (![X19 : $i, X20 : $i]:
% 0.67/0.87         (((X19) = (o_0_0_xboole_0))
% 0.67/0.87          | ~ (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.67/0.87      inference('demod', [status(thm)], ['14', '15'])).
% 0.67/0.87  thf('106', plain, (((k4_xboole_0 @ sk_A @ sk_A) = (o_0_0_xboole_0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['104', '105'])).
% 0.67/0.87  thf('107', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.67/0.87      inference('demod', [status(thm)], ['101', '106'])).
% 0.67/0.87  thf('108', plain, ($false), inference('sup-', [status(thm)], ['74', '107'])).
% 0.67/0.87  
% 0.67/0.87  % SZS output end Refutation
% 0.67/0.87  
% 0.67/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
