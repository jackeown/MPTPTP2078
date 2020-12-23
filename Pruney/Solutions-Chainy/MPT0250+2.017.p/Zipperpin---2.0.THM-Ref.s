%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yzwpt8Ln6P

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:49 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 115 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  705 (1032 expanded)
%              Number of equality atoms :   51 (  77 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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

thf('1',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X31 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) )
      | ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X22 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X44 ) @ X45 )
      | ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('30',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X44 ) @ X45 )
      | ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('31',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('41',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','38','39','40'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X11 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( ( k1_tarski @ sk_A )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( ( k1_tarski @ sk_A )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(condensation,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yzwpt8Ln6P
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.27/1.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.27/1.52  % Solved by: fo/fo7.sh
% 1.27/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.52  % done 1250 iterations in 1.072s
% 1.27/1.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.27/1.52  % SZS output start Refutation
% 1.27/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.27/1.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.27/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.52  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.27/1.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.27/1.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.27/1.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.27/1.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.27/1.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.27/1.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.27/1.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.27/1.52  thf(t70_enumset1, axiom,
% 1.27/1.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.27/1.52  thf('0', plain,
% 1.27/1.52      (![X35 : $i, X36 : $i]:
% 1.27/1.52         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 1.27/1.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.27/1.52  thf(d1_enumset1, axiom,
% 1.27/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.27/1.52       ( ![E:$i]:
% 1.27/1.52         ( ( r2_hidden @ E @ D ) <=>
% 1.27/1.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.27/1.52  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.27/1.52  thf(zf_stmt_1, axiom,
% 1.27/1.52    (![E:$i,C:$i,B:$i,A:$i]:
% 1.27/1.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.27/1.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.27/1.52  thf(zf_stmt_2, axiom,
% 1.27/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.27/1.52       ( ![E:$i]:
% 1.27/1.52         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.27/1.52  thf('1', plain,
% 1.27/1.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.27/1.52         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 1.27/1.52          | (r2_hidden @ X27 @ X31)
% 1.27/1.52          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 1.27/1.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.27/1.52  thf('2', plain,
% 1.27/1.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.27/1.52         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 1.27/1.52          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 1.27/1.52      inference('simplify', [status(thm)], ['1'])).
% 1.27/1.52  thf('3', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.27/1.52          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.27/1.52      inference('sup+', [status(thm)], ['0', '2'])).
% 1.27/1.52  thf('4', plain,
% 1.27/1.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.27/1.52         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 1.27/1.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.27/1.52  thf('5', plain,
% 1.27/1.52      (![X22 : $i, X24 : $i, X25 : $i]:
% 1.27/1.52         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 1.27/1.52      inference('simplify', [status(thm)], ['4'])).
% 1.27/1.52  thf('6', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.27/1.52      inference('sup-', [status(thm)], ['3', '5'])).
% 1.27/1.52  thf(t69_enumset1, axiom,
% 1.27/1.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.27/1.52  thf('7', plain, (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 1.27/1.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.27/1.52  thf(d5_xboole_0, axiom,
% 1.27/1.52    (![A:$i,B:$i,C:$i]:
% 1.27/1.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.27/1.52       ( ![D:$i]:
% 1.27/1.52         ( ( r2_hidden @ D @ C ) <=>
% 1.27/1.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.27/1.52  thf('8', plain,
% 1.27/1.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.27/1.52         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.27/1.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.27/1.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.27/1.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.27/1.52  thf('9', plain,
% 1.27/1.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.27/1.52         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.27/1.52          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.27/1.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.27/1.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.27/1.52  thf('10', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.27/1.52          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.27/1.52          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.27/1.52          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['8', '9'])).
% 1.27/1.52  thf('11', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.27/1.52          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.27/1.52      inference('simplify', [status(thm)], ['10'])).
% 1.27/1.52  thf('12', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.27/1.52          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.27/1.52      inference('simplify', [status(thm)], ['10'])).
% 1.27/1.52  thf(l27_zfmisc_1, axiom,
% 1.27/1.52    (![A:$i,B:$i]:
% 1.27/1.52     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.27/1.52  thf('13', plain,
% 1.27/1.52      (![X44 : $i, X45 : $i]:
% 1.27/1.52         ((r1_xboole_0 @ (k1_tarski @ X44) @ X45) | (r2_hidden @ X44 @ X45))),
% 1.27/1.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.27/1.52  thf(t83_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i]:
% 1.27/1.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.27/1.52  thf('14', plain,
% 1.27/1.52      (![X17 : $i, X18 : $i]:
% 1.27/1.52         (((k4_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_xboole_0 @ X17 @ X18))),
% 1.27/1.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.27/1.52  thf('15', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((r2_hidden @ X1 @ X0)
% 1.27/1.52          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['13', '14'])).
% 1.27/1.52  thf('16', plain,
% 1.27/1.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X4 @ X3)
% 1.27/1.52          | ~ (r2_hidden @ X4 @ X2)
% 1.27/1.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.27/1.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.27/1.52  thf('17', plain,
% 1.27/1.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X4 @ X2)
% 1.27/1.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.27/1.52      inference('simplify', [status(thm)], ['16'])).
% 1.27/1.52  thf('18', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 1.27/1.52          | (r2_hidden @ X0 @ X1)
% 1.27/1.52          | ~ (r2_hidden @ X2 @ X1))),
% 1.27/1.52      inference('sup-', [status(thm)], ['15', '17'])).
% 1.27/1.52  thf('19', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.27/1.52          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X2)
% 1.27/1.52          | (r2_hidden @ X0 @ X2))),
% 1.27/1.52      inference('sup-', [status(thm)], ['12', '18'])).
% 1.27/1.52  thf('20', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.27/1.52          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.27/1.52          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['11', '19'])).
% 1.27/1.52  thf('21', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.27/1.52          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.27/1.52      inference('simplify', [status(thm)], ['20'])).
% 1.27/1.52  thf('22', plain,
% 1.27/1.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X4 @ X2)
% 1.27/1.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.27/1.52      inference('simplify', [status(thm)], ['16'])).
% 1.27/1.52  thf('23', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 1.27/1.52          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.27/1.52          | ~ (r2_hidden @ X2 @ X1))),
% 1.27/1.52      inference('sup-', [status(thm)], ['21', '22'])).
% 1.27/1.52  thf('24', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.27/1.52          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.27/1.52      inference('condensation', [status(thm)], ['23'])).
% 1.27/1.52  thf('25', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 1.27/1.52          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['7', '24'])).
% 1.27/1.52  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['6', '25'])).
% 1.27/1.52  thf('27', plain,
% 1.27/1.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.27/1.52         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.27/1.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.27/1.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.27/1.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.27/1.52  thf('28', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.27/1.52          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.27/1.52      inference('eq_fact', [status(thm)], ['27'])).
% 1.27/1.52  thf('29', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.27/1.52          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.27/1.52      inference('eq_fact', [status(thm)], ['27'])).
% 1.27/1.52  thf('30', plain,
% 1.27/1.52      (![X44 : $i, X45 : $i]:
% 1.27/1.52         ((r1_xboole_0 @ (k1_tarski @ X44) @ X45) | (r2_hidden @ X44 @ X45))),
% 1.27/1.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.27/1.52  thf(t45_zfmisc_1, conjecture,
% 1.27/1.52    (![A:$i,B:$i]:
% 1.27/1.52     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.27/1.52       ( r2_hidden @ A @ B ) ))).
% 1.27/1.52  thf(zf_stmt_3, negated_conjecture,
% 1.27/1.52    (~( ![A:$i,B:$i]:
% 1.27/1.52        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.27/1.52          ( r2_hidden @ A @ B ) ) )),
% 1.27/1.52    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 1.27/1.52  thf('31', plain,
% 1.27/1.52      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 1.27/1.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.27/1.52  thf(d10_xboole_0, axiom,
% 1.27/1.52    (![A:$i,B:$i]:
% 1.27/1.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.27/1.52  thf('32', plain,
% 1.27/1.52      (![X6 : $i, X8 : $i]:
% 1.27/1.52         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.27/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.27/1.52  thf('33', plain,
% 1.27/1.52      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 1.27/1.52        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['31', '32'])).
% 1.27/1.52  thf(commutativity_k2_tarski, axiom,
% 1.27/1.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.27/1.52  thf('34', plain,
% 1.27/1.52      (![X20 : $i, X21 : $i]:
% 1.27/1.52         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.27/1.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.27/1.52  thf(l51_zfmisc_1, axiom,
% 1.27/1.52    (![A:$i,B:$i]:
% 1.27/1.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.27/1.52  thf('35', plain,
% 1.27/1.52      (![X46 : $i, X47 : $i]:
% 1.27/1.52         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 1.27/1.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.27/1.52  thf('36', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.27/1.52      inference('sup+', [status(thm)], ['34', '35'])).
% 1.27/1.52  thf('37', plain,
% 1.27/1.52      (![X46 : $i, X47 : $i]:
% 1.27/1.52         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 1.27/1.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.27/1.52  thf('38', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.27/1.52      inference('sup+', [status(thm)], ['36', '37'])).
% 1.27/1.52  thf(t7_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.27/1.52  thf('39', plain,
% 1.27/1.52      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.27/1.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.27/1.52  thf('40', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.27/1.52      inference('sup+', [status(thm)], ['36', '37'])).
% 1.27/1.52  thf('41', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.27/1.52      inference('demod', [status(thm)], ['33', '38', '39', '40'])).
% 1.27/1.52  thf(t70_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i,C:$i]:
% 1.27/1.52     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.27/1.52            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.27/1.52       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.27/1.52            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.27/1.52  thf('42', plain,
% 1.27/1.52      (![X11 : $i, X12 : $i, X14 : $i]:
% 1.27/1.52         ((r1_xboole_0 @ X11 @ X14)
% 1.27/1.52          | ~ (r1_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X14)))),
% 1.27/1.52      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.27/1.52  thf('43', plain,
% 1.27/1.52      (![X0 : $i]:
% 1.27/1.52         (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['41', '42'])).
% 1.27/1.52  thf('44', plain,
% 1.27/1.52      (![X0 : $i]:
% 1.27/1.52         ((r2_hidden @ X0 @ sk_B)
% 1.27/1.52          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['30', '43'])).
% 1.27/1.52  thf('45', plain,
% 1.27/1.52      (![X17 : $i, X18 : $i]:
% 1.27/1.52         (((k4_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_xboole_0 @ X17 @ X18))),
% 1.27/1.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.27/1.52  thf('46', plain,
% 1.27/1.52      (![X0 : $i]:
% 1.27/1.52         ((r2_hidden @ X0 @ sk_B)
% 1.27/1.52          | ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A))
% 1.27/1.52              = (k1_tarski @ X0)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['44', '45'])).
% 1.27/1.52  thf('47', plain,
% 1.27/1.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X4 @ X2)
% 1.27/1.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.27/1.52      inference('simplify', [status(thm)], ['16'])).
% 1.27/1.52  thf('48', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.27/1.52          | (r2_hidden @ X0 @ sk_B)
% 1.27/1.52          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['46', '47'])).
% 1.27/1.52  thf('49', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         (((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 1.27/1.52          | (r2_hidden @ X1 @ sk_B)
% 1.27/1.52          | ~ (r2_hidden @ 
% 1.27/1.52               (sk_D @ (k1_tarski @ sk_A) @ X0 @ (k1_tarski @ sk_A)) @ 
% 1.27/1.52               (k1_tarski @ X1)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['29', '48'])).
% 1.27/1.52  thf('50', plain,
% 1.27/1.52      (![X0 : $i]:
% 1.27/1.52         (((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 1.27/1.52          | (r2_hidden @ sk_A @ sk_B)
% 1.27/1.52          | ((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 1.27/1.52      inference('sup-', [status(thm)], ['28', '49'])).
% 1.27/1.52  thf('51', plain,
% 1.27/1.52      (![X0 : $i]:
% 1.27/1.52         ((r2_hidden @ sk_A @ sk_B)
% 1.27/1.52          | ((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 1.27/1.52      inference('simplify', [status(thm)], ['50'])).
% 1.27/1.52  thf('52', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.27/1.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.27/1.52  thf('53', plain,
% 1.27/1.52      (![X0 : $i]:
% 1.27/1.52         ((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 1.27/1.52      inference('clc', [status(thm)], ['51', '52'])).
% 1.27/1.52  thf('54', plain,
% 1.27/1.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X4 @ X2)
% 1.27/1.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.27/1.52      inference('simplify', [status(thm)], ['16'])).
% 1.27/1.52  thf('55', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         (~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X1 @ X0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['53', '54'])).
% 1.27/1.52  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 1.27/1.52      inference('condensation', [status(thm)], ['55'])).
% 1.27/1.52  thf('57', plain, ($false), inference('sup-', [status(thm)], ['26', '56'])).
% 1.27/1.52  
% 1.27/1.52  % SZS output end Refutation
% 1.27/1.52  
% 1.27/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
