%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EXoRPiEGEs

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:53 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 316 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :   22
%              Number of atoms          : 1264 (3216 expanded)
%              Number of equality atoms :  110 ( 271 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('16',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('17',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X43 ) @ X44 )
      | ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X20 )
      | ( ( k4_xboole_0 @ X18 @ X20 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','54'])).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('72',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['76'])).

thf('81',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('83',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('84',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ k1_xboole_0 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['78','81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('87',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','97'])).

thf('99',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','108'])).

thf('110',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('116',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','68','69','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EXoRPiEGEs
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.50/3.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.50/3.75  % Solved by: fo/fo7.sh
% 3.50/3.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.50/3.75  % done 3915 iterations in 3.295s
% 3.50/3.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.50/3.75  % SZS output start Refutation
% 3.50/3.75  thf(sk_A_type, type, sk_A: $i).
% 3.50/3.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.50/3.75  thf(sk_B_type, type, sk_B: $i > $i).
% 3.50/3.75  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.50/3.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.50/3.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.50/3.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.50/3.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.50/3.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 3.50/3.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.50/3.75  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.50/3.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.50/3.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.50/3.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.50/3.75  thf(t65_zfmisc_1, conjecture,
% 3.50/3.75    (![A:$i,B:$i]:
% 3.50/3.75     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 3.50/3.75       ( ~( r2_hidden @ B @ A ) ) ))).
% 3.50/3.75  thf(zf_stmt_0, negated_conjecture,
% 3.50/3.75    (~( ![A:$i,B:$i]:
% 3.50/3.75        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 3.50/3.75          ( ~( r2_hidden @ B @ A ) ) ) )),
% 3.50/3.75    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 3.50/3.75  thf('0', plain,
% 3.50/3.75      (((r2_hidden @ sk_B_1 @ sk_A)
% 3.50/3.75        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 3.50/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.75  thf('1', plain,
% 3.50/3.75      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 3.50/3.75       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 3.50/3.75      inference('split', [status(esa)], ['0'])).
% 3.50/3.75  thf('2', plain,
% 3.50/3.75      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 3.50/3.75      inference('split', [status(esa)], ['0'])).
% 3.50/3.75  thf(t70_enumset1, axiom,
% 3.50/3.75    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.50/3.75  thf('3', plain,
% 3.50/3.75      (![X34 : $i, X35 : $i]:
% 3.50/3.75         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 3.50/3.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.50/3.75  thf(d1_enumset1, axiom,
% 3.50/3.75    (![A:$i,B:$i,C:$i,D:$i]:
% 3.50/3.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.50/3.75       ( ![E:$i]:
% 3.50/3.75         ( ( r2_hidden @ E @ D ) <=>
% 3.50/3.75           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 3.50/3.75  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 3.50/3.75  thf(zf_stmt_2, axiom,
% 3.50/3.75    (![E:$i,C:$i,B:$i,A:$i]:
% 3.50/3.75     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 3.50/3.75       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 3.50/3.75  thf(zf_stmt_3, axiom,
% 3.50/3.75    (![A:$i,B:$i,C:$i,D:$i]:
% 3.50/3.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.50/3.75       ( ![E:$i]:
% 3.50/3.75         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 3.50/3.75  thf('4', plain,
% 3.50/3.75      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.50/3.75         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 3.50/3.75          | (r2_hidden @ X26 @ X30)
% 3.50/3.75          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 3.50/3.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.50/3.75  thf('5', plain,
% 3.50/3.75      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.50/3.75         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 3.50/3.75          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 3.50/3.75      inference('simplify', [status(thm)], ['4'])).
% 3.50/3.75  thf('6', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 3.50/3.75          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 3.50/3.75      inference('sup+', [status(thm)], ['3', '5'])).
% 3.50/3.75  thf('7', plain,
% 3.50/3.75      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.50/3.75         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 3.50/3.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.50/3.75  thf('8', plain,
% 3.50/3.75      (![X21 : $i, X23 : $i, X24 : $i]:
% 3.50/3.75         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 3.50/3.75      inference('simplify', [status(thm)], ['7'])).
% 3.50/3.75  thf('9', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 3.50/3.75      inference('sup-', [status(thm)], ['6', '8'])).
% 3.50/3.75  thf(t69_enumset1, axiom,
% 3.50/3.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.50/3.75  thf('10', plain,
% 3.50/3.75      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 3.50/3.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.50/3.75  thf(t7_xboole_0, axiom,
% 3.50/3.75    (![A:$i]:
% 3.50/3.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.50/3.75          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 3.50/3.75  thf('11', plain,
% 3.50/3.75      (![X14 : $i]:
% 3.50/3.75         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 3.50/3.75      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.50/3.75  thf(d5_xboole_0, axiom,
% 3.50/3.75    (![A:$i,B:$i,C:$i]:
% 3.50/3.75     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.50/3.75       ( ![D:$i]:
% 3.50/3.75         ( ( r2_hidden @ D @ C ) <=>
% 3.50/3.75           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.50/3.75  thf('12', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X12 @ X11)
% 3.50/3.75          | (r2_hidden @ X12 @ X9)
% 3.50/3.75          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.50/3.75  thf('13', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.50/3.75         ((r2_hidden @ X12 @ X9)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['12'])).
% 3.50/3.75  thf('14', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 3.50/3.75          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 3.50/3.75      inference('sup-', [status(thm)], ['11', '13'])).
% 3.50/3.75  thf('15', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 3.50/3.75          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 3.50/3.75      inference('sup-', [status(thm)], ['11', '13'])).
% 3.50/3.75  thf('16', plain,
% 3.50/3.75      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 3.50/3.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.50/3.75  thf(l27_zfmisc_1, axiom,
% 3.50/3.75    (![A:$i,B:$i]:
% 3.50/3.75     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 3.50/3.75  thf('17', plain,
% 3.50/3.75      (![X43 : $i, X44 : $i]:
% 3.50/3.75         ((r1_xboole_0 @ (k1_tarski @ X43) @ X44) | (r2_hidden @ X43 @ X44))),
% 3.50/3.75      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 3.50/3.75  thf(t83_xboole_1, axiom,
% 3.50/3.75    (![A:$i,B:$i]:
% 3.50/3.75     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.50/3.75  thf('18', plain,
% 3.50/3.75      (![X18 : $i, X19 : $i]:
% 3.50/3.75         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 3.50/3.75      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.50/3.75  thf('19', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ X1 @ X0)
% 3.50/3.75          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['17', '18'])).
% 3.50/3.75  thf('20', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) = (k1_tarski @ X0))
% 3.50/3.75          | (r2_hidden @ X0 @ X1))),
% 3.50/3.75      inference('sup+', [status(thm)], ['16', '19'])).
% 3.50/3.75  thf('21', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X12 @ X11)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ X10)
% 3.50/3.75          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.50/3.75  thf('22', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X12 @ X10)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['21'])).
% 3.50/3.75  thf('23', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 3.50/3.75          | (r2_hidden @ X0 @ X1)
% 3.50/3.75          | ~ (r2_hidden @ X2 @ X1))),
% 3.50/3.75      inference('sup-', [status(thm)], ['20', '22'])).
% 3.50/3.75  thf('24', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 3.50/3.75          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) @ X2)
% 3.50/3.75          | (r2_hidden @ X0 @ X2))),
% 3.50/3.75      inference('sup-', [status(thm)], ['15', '23'])).
% 3.50/3.75  thf('25', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 3.50/3.75          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 3.50/3.75          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['14', '24'])).
% 3.50/3.75  thf('26', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 3.50/3.75          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['25'])).
% 3.50/3.75  thf('27', plain,
% 3.50/3.75      (![X18 : $i, X20 : $i]:
% 3.50/3.75         ((r1_xboole_0 @ X18 @ X20) | ((k4_xboole_0 @ X18 @ X20) != (X18)))),
% 3.50/3.75      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.50/3.75  thf('28', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((k1_xboole_0) != (k1_tarski @ X0))
% 3.50/3.75          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 3.50/3.75          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 3.50/3.75      inference('sup-', [status(thm)], ['26', '27'])).
% 3.50/3.75  thf(d4_xboole_0, axiom,
% 3.50/3.75    (![A:$i,B:$i,C:$i]:
% 3.50/3.75     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.50/3.75       ( ![D:$i]:
% 3.50/3.75         ( ( r2_hidden @ D @ C ) <=>
% 3.50/3.75           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.50/3.75  thf('29', plain,
% 3.50/3.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 3.50/3.75         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 3.50/3.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 3.50/3.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 3.50/3.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.50/3.75  thf('30', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.50/3.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('eq_fact', [status(thm)], ['29'])).
% 3.50/3.75  thf('31', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.50/3.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('eq_fact', [status(thm)], ['29'])).
% 3.50/3.75  thf('32', plain,
% 3.50/3.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 3.50/3.75         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 3.50/3.75          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 3.50/3.75          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 3.50/3.75          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 3.50/3.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.50/3.75  thf('33', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.50/3.75          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.50/3.75          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 3.50/3.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['31', '32'])).
% 3.50/3.75  thf('34', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 3.50/3.75          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.50/3.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['33'])).
% 3.50/3.75  thf('35', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.50/3.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('eq_fact', [status(thm)], ['29'])).
% 3.50/3.75  thf('36', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.50/3.75          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 3.50/3.75      inference('clc', [status(thm)], ['34', '35'])).
% 3.50/3.75  thf('37', plain,
% 3.50/3.75      (![X0 : $i]:
% 3.50/3.75         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['30', '36'])).
% 3.50/3.75  thf('38', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 3.50/3.75      inference('simplify', [status(thm)], ['37'])).
% 3.50/3.75  thf(commutativity_k3_xboole_0, axiom,
% 3.50/3.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.50/3.75  thf('39', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.75  thf(t100_xboole_1, axiom,
% 3.50/3.75    (![A:$i,B:$i]:
% 3.50/3.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.50/3.75  thf('40', plain,
% 3.50/3.75      (![X15 : $i, X16 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X15 @ X16)
% 3.50/3.75           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 3.50/3.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.50/3.75  thf('41', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X0 @ X1)
% 3.50/3.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('sup+', [status(thm)], ['39', '40'])).
% 3.50/3.75  thf('42', plain,
% 3.50/3.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.50/3.75      inference('sup+', [status(thm)], ['38', '41'])).
% 3.50/3.75  thf('43', plain,
% 3.50/3.75      (![X14 : $i]:
% 3.50/3.75         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 3.50/3.75      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.50/3.75  thf('44', plain,
% 3.50/3.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.50/3.75      inference('sup+', [status(thm)], ['38', '41'])).
% 3.50/3.75  thf('45', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.50/3.75         ((r2_hidden @ X12 @ X9)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['12'])).
% 3.50/3.75  thf('46', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['44', '45'])).
% 3.50/3.75  thf('47', plain,
% 3.50/3.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.50/3.75      inference('sup+', [status(thm)], ['38', '41'])).
% 3.50/3.75  thf('48', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X12 @ X10)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['21'])).
% 3.50/3.75  thf('49', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 3.50/3.75          | ~ (r2_hidden @ X1 @ X0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['47', '48'])).
% 3.50/3.75  thf('50', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 3.50/3.75      inference('clc', [status(thm)], ['46', '49'])).
% 3.50/3.75  thf('51', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['43', '50'])).
% 3.50/3.75  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.50/3.75      inference('demod', [status(thm)], ['42', '51'])).
% 3.50/3.75  thf('53', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ X1 @ X0)
% 3.50/3.75          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['17', '18'])).
% 3.50/3.75  thf('54', plain,
% 3.50/3.75      (![X0 : $i]:
% 3.50/3.75         (((k1_xboole_0) = (k1_tarski @ X0))
% 3.50/3.75          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 3.50/3.75      inference('sup+', [status(thm)], ['52', '53'])).
% 3.50/3.75  thf('55', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 3.50/3.75          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 3.50/3.75      inference('clc', [status(thm)], ['28', '54'])).
% 3.50/3.75  thf('56', plain,
% 3.50/3.75      (![X18 : $i, X19 : $i]:
% 3.50/3.75         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 3.50/3.75      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.50/3.75  thf('57', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ X1 @ (k1_tarski @ X1))
% 3.50/3.75          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['55', '56'])).
% 3.50/3.75  thf('58', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X12 @ X10)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['21'])).
% 3.50/3.75  thf('59', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 3.50/3.75          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 3.50/3.75          | ~ (r2_hidden @ X2 @ X1))),
% 3.50/3.75      inference('sup-', [status(thm)], ['57', '58'])).
% 3.50/3.75  thf('60', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 3.50/3.75          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 3.50/3.75      inference('condensation', [status(thm)], ['59'])).
% 3.50/3.75  thf('61', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 3.50/3.75          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['10', '60'])).
% 3.50/3.75  thf('62', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['9', '61'])).
% 3.50/3.75  thf('63', plain,
% 3.50/3.75      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 3.50/3.75        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 3.50/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.75  thf('64', plain,
% 3.50/3.75      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 3.50/3.75         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 3.50/3.75      inference('split', [status(esa)], ['63'])).
% 3.50/3.75  thf('65', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X12 @ X10)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['21'])).
% 3.50/3.75  thf('66', plain,
% 3.50/3.75      ((![X0 : $i]:
% 3.50/3.75          (~ (r2_hidden @ X0 @ sk_A)
% 3.50/3.75           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1))))
% 3.50/3.75         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 3.50/3.75      inference('sup-', [status(thm)], ['64', '65'])).
% 3.50/3.75  thf('67', plain,
% 3.50/3.75      ((~ (r2_hidden @ sk_B_1 @ sk_A))
% 3.50/3.75         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 3.50/3.75      inference('sup-', [status(thm)], ['62', '66'])).
% 3.50/3.75  thf('68', plain,
% 3.50/3.75      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 3.50/3.75       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['2', '67'])).
% 3.50/3.75  thf('69', plain,
% 3.50/3.75      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 3.50/3.75       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 3.50/3.75      inference('split', [status(esa)], ['63'])).
% 3.50/3.75  thf('70', plain,
% 3.50/3.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 3.50/3.75         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 3.50/3.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 3.50/3.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 3.50/3.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.50/3.75  thf('71', plain,
% 3.50/3.75      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X6 @ X5)
% 3.50/3.75          | (r2_hidden @ X6 @ X4)
% 3.50/3.75          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 3.50/3.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.50/3.75  thf('72', plain,
% 3.50/3.75      (![X3 : $i, X4 : $i, X6 : $i]:
% 3.50/3.75         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['71'])).
% 3.50/3.75  thf('73', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.50/3.75         ((r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 3.50/3.75          | ((X3) = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 3.50/3.75          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['70', '72'])).
% 3.50/3.75  thf(t3_boole, axiom,
% 3.50/3.75    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.50/3.75  thf('74', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.50/3.75      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.75  thf('75', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X12 @ X10)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['21'])).
% 3.50/3.75  thf('76', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['74', '75'])).
% 3.50/3.75  thf('77', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.50/3.75      inference('condensation', [status(thm)], ['76'])).
% 3.50/3.75  thf('78', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         (((X2) = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))
% 3.50/3.75          | (r2_hidden @ (sk_D @ X2 @ (k3_xboole_0 @ X1 @ k1_xboole_0) @ X0) @ 
% 3.50/3.75             X2))),
% 3.50/3.75      inference('sup-', [status(thm)], ['73', '77'])).
% 3.50/3.75  thf('79', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.50/3.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('eq_fact', [status(thm)], ['29'])).
% 3.50/3.75  thf('80', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.50/3.75      inference('condensation', [status(thm)], ['76'])).
% 3.50/3.75  thf('81', plain,
% 3.50/3.75      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['79', '80'])).
% 3.50/3.75  thf('82', plain,
% 3.50/3.75      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['79', '80'])).
% 3.50/3.75  thf('83', plain,
% 3.50/3.75      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['79', '80'])).
% 3.50/3.75  thf('84', plain,
% 3.50/3.75      (![X0 : $i, X2 : $i]:
% 3.50/3.75         (((X2) = (k1_xboole_0))
% 3.50/3.75          | (r2_hidden @ (sk_D @ X2 @ k1_xboole_0 @ X0) @ X2))),
% 3.50/3.75      inference('demod', [status(thm)], ['78', '81', '82', '83'])).
% 3.50/3.75  thf('85', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ X1 @ X0)
% 3.50/3.75          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['17', '18'])).
% 3.50/3.75  thf('86', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.50/3.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('eq_fact', [status(thm)], ['29'])).
% 3.50/3.75  thf('87', plain,
% 3.50/3.75      (![X3 : $i, X4 : $i, X6 : $i]:
% 3.50/3.75         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['71'])).
% 3.50/3.75  thf('88', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         (((k3_xboole_0 @ X1 @ X0)
% 3.50/3.75            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 3.50/3.75          | (r2_hidden @ 
% 3.50/3.75             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 3.50/3.75             X0))),
% 3.50/3.75      inference('sup-', [status(thm)], ['86', '87'])).
% 3.50/3.75  thf('89', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.50/3.75          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 3.50/3.75      inference('clc', [status(thm)], ['34', '35'])).
% 3.50/3.75  thf('90', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((k3_xboole_0 @ X1 @ X0)
% 3.50/3.75            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 3.50/3.75          | ((k3_xboole_0 @ X1 @ X0)
% 3.50/3.75              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.50/3.75      inference('sup-', [status(thm)], ['88', '89'])).
% 3.50/3.75  thf('91', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k3_xboole_0 @ X1 @ X0)
% 3.50/3.75           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['90'])).
% 3.50/3.75  thf('92', plain,
% 3.50/3.75      (![X15 : $i, X16 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X15 @ X16)
% 3.50/3.75           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 3.50/3.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.50/3.75  thf('93', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.50/3.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('sup+', [status(thm)], ['91', '92'])).
% 3.50/3.75  thf('94', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X0 @ X1)
% 3.50/3.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('sup+', [status(thm)], ['39', '40'])).
% 3.50/3.75  thf('95', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.50/3.75           = (k4_xboole_0 @ X0 @ X1))),
% 3.50/3.75      inference('demod', [status(thm)], ['93', '94'])).
% 3.50/3.75  thf('96', plain,
% 3.50/3.75      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X12 @ X10)
% 3.50/3.75          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['21'])).
% 3.50/3.75  thf('97', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.50/3.75          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['95', '96'])).
% 3.50/3.75  thf('98', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 3.50/3.75          | (r2_hidden @ X0 @ X1)
% 3.50/3.75          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 3.50/3.75      inference('sup-', [status(thm)], ['85', '97'])).
% 3.50/3.75  thf('99', plain,
% 3.50/3.75      (![X3 : $i, X4 : $i, X6 : $i]:
% 3.50/3.75         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['71'])).
% 3.50/3.75  thf('100', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 3.50/3.75          | (r2_hidden @ X0 @ X1))),
% 3.50/3.75      inference('clc', [status(thm)], ['98', '99'])).
% 3.50/3.75  thf('101', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 3.50/3.75          | (r2_hidden @ X0 @ X1))),
% 3.50/3.75      inference('sup-', [status(thm)], ['84', '100'])).
% 3.50/3.75  thf('102', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.75  thf('103', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k3_xboole_0 @ X1 @ X0)
% 3.50/3.75           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('simplify', [status(thm)], ['90'])).
% 3.50/3.75  thf('104', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k3_xboole_0 @ X0 @ X1)
% 3.50/3.75           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('sup+', [status(thm)], ['102', '103'])).
% 3.50/3.75  thf('105', plain,
% 3.50/3.75      (![X15 : $i, X16 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X15 @ X16)
% 3.50/3.75           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 3.50/3.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.50/3.75  thf('106', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 3.50/3.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('sup+', [status(thm)], ['104', '105'])).
% 3.50/3.75  thf('107', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X0 @ X1)
% 3.50/3.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.50/3.75      inference('sup+', [status(thm)], ['39', '40'])).
% 3.50/3.75  thf('108', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 3.50/3.75           = (k4_xboole_0 @ X0 @ X1))),
% 3.50/3.75      inference('demod', [status(thm)], ['106', '107'])).
% 3.50/3.75  thf('109', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((k4_xboole_0 @ X1 @ k1_xboole_0)
% 3.50/3.75            = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 3.50/3.75          | (r2_hidden @ X0 @ X1))),
% 3.50/3.75      inference('sup+', [status(thm)], ['101', '108'])).
% 3.50/3.75  thf('110', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.50/3.75      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.75  thf('111', plain,
% 3.50/3.75      (![X0 : $i, X1 : $i]:
% 3.50/3.75         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 3.50/3.75          | (r2_hidden @ X0 @ X1))),
% 3.50/3.75      inference('demod', [status(thm)], ['109', '110'])).
% 3.50/3.75  thf('112', plain,
% 3.50/3.75      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 3.50/3.75         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 3.50/3.75      inference('split', [status(esa)], ['0'])).
% 3.50/3.75  thf('113', plain,
% 3.50/3.75      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A)))
% 3.50/3.75         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 3.50/3.75      inference('sup-', [status(thm)], ['111', '112'])).
% 3.50/3.75  thf('114', plain,
% 3.50/3.75      (((r2_hidden @ sk_B_1 @ sk_A))
% 3.50/3.75         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 3.50/3.75      inference('simplify', [status(thm)], ['113'])).
% 3.50/3.75  thf('115', plain,
% 3.50/3.75      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 3.50/3.75      inference('split', [status(esa)], ['63'])).
% 3.50/3.75  thf('116', plain,
% 3.50/3.75      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 3.50/3.75       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 3.50/3.75      inference('sup-', [status(thm)], ['114', '115'])).
% 3.50/3.75  thf('117', plain, ($false),
% 3.50/3.75      inference('sat_resolution*', [status(thm)], ['1', '68', '69', '116'])).
% 3.50/3.75  
% 3.50/3.75  % SZS output end Refutation
% 3.50/3.75  
% 3.60/3.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
