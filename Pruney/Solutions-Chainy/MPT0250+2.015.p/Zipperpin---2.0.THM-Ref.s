%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bsmbah1o0B

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:49 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 273 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  757 (2550 expanded)
%              Number of equality atoms :   50 ( 162 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
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

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X34 @ X38 )
      | ( X38
       != ( k1_enumset1 @ X37 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k1_enumset1 @ X37 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ~ ( zip_tseitin_0 @ X29 @ X31 @ X32 @ X29 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 )
      | ( X30 = X31 )
      | ( X30 = X32 )
      | ( X30 = X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ X38 )
      | ~ ( zip_tseitin_0 @ X39 @ X35 @ X36 @ X37 )
      | ( X38
       != ( k1_enumset1 @ X37 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    ! [X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X35 @ X36 @ X37 )
      | ~ ( r2_hidden @ X39 @ ( k1_enumset1 @ X37 @ X36 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('23',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('33',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','30','31','32'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X19 @ X22 )
      | ~ ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('46',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('49',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('59',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('64',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('sup-',[status(thm)],['8','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bsmbah1o0B
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.97/2.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.97/2.17  % Solved by: fo/fo7.sh
% 1.97/2.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.17  % done 1877 iterations in 1.708s
% 1.97/2.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.97/2.17  % SZS output start Refutation
% 1.97/2.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.97/2.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.97/2.17  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.97/2.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.97/2.17  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.97/2.17  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.97/2.17  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.97/2.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.97/2.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.97/2.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.97/2.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.97/2.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.17  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.97/2.17  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.97/2.17  thf(t69_enumset1, axiom,
% 1.97/2.17    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.97/2.17  thf('0', plain, (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 1.97/2.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.97/2.17  thf(t70_enumset1, axiom,
% 1.97/2.17    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.97/2.17  thf('1', plain,
% 1.97/2.17      (![X42 : $i, X43 : $i]:
% 1.97/2.17         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 1.97/2.17      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.97/2.17  thf(d1_enumset1, axiom,
% 1.97/2.17    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.17     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.97/2.17       ( ![E:$i]:
% 1.97/2.17         ( ( r2_hidden @ E @ D ) <=>
% 1.97/2.17           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.97/2.17  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.97/2.17  thf(zf_stmt_1, axiom,
% 1.97/2.17    (![E:$i,C:$i,B:$i,A:$i]:
% 1.97/2.17     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.97/2.17       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.97/2.17  thf(zf_stmt_2, axiom,
% 1.97/2.17    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.17     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.97/2.17       ( ![E:$i]:
% 1.97/2.17         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.97/2.17  thf('2', plain,
% 1.97/2.17      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.97/2.17         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 1.97/2.17          | (r2_hidden @ X34 @ X38)
% 1.97/2.17          | ((X38) != (k1_enumset1 @ X37 @ X36 @ X35)))),
% 1.97/2.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.97/2.17  thf('3', plain,
% 1.97/2.17      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.97/2.17         ((r2_hidden @ X34 @ (k1_enumset1 @ X37 @ X36 @ X35))
% 1.97/2.17          | (zip_tseitin_0 @ X34 @ X35 @ X36 @ X37))),
% 1.97/2.17      inference('simplify', [status(thm)], ['2'])).
% 1.97/2.17  thf('4', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.17         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.97/2.17          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.97/2.17      inference('sup+', [status(thm)], ['1', '3'])).
% 1.97/2.17  thf('5', plain,
% 1.97/2.17      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.97/2.17         (((X30) != (X29)) | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 1.97/2.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.17  thf('6', plain,
% 1.97/2.17      (![X29 : $i, X31 : $i, X32 : $i]:
% 1.97/2.17         ~ (zip_tseitin_0 @ X29 @ X31 @ X32 @ X29)),
% 1.97/2.17      inference('simplify', [status(thm)], ['5'])).
% 1.97/2.17  thf('7', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.97/2.17      inference('sup-', [status(thm)], ['4', '6'])).
% 1.97/2.17  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.97/2.17      inference('sup+', [status(thm)], ['0', '7'])).
% 1.97/2.17  thf('9', plain,
% 1.97/2.17      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.97/2.17         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 1.97/2.17          | ((X30) = (X31))
% 1.97/2.17          | ((X30) = (X32))
% 1.97/2.17          | ((X30) = (X33)))),
% 1.97/2.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.17  thf(t3_xboole_0, axiom,
% 1.97/2.17    (![A:$i,B:$i]:
% 1.97/2.17     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.97/2.17            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.97/2.17       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.97/2.17            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.97/2.17  thf('10', plain,
% 1.97/2.17      (![X10 : $i, X11 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 1.97/2.17      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.97/2.17  thf('11', plain,
% 1.97/2.17      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 1.97/2.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.97/2.17  thf('12', plain,
% 1.97/2.17      (![X42 : $i, X43 : $i]:
% 1.97/2.17         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 1.97/2.17      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.97/2.17  thf('13', plain,
% 1.97/2.17      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X39 @ X38)
% 1.97/2.17          | ~ (zip_tseitin_0 @ X39 @ X35 @ X36 @ X37)
% 1.97/2.17          | ((X38) != (k1_enumset1 @ X37 @ X36 @ X35)))),
% 1.97/2.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.97/2.17  thf('14', plain,
% 1.97/2.17      (![X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 1.97/2.17         (~ (zip_tseitin_0 @ X39 @ X35 @ X36 @ X37)
% 1.97/2.17          | ~ (r2_hidden @ X39 @ (k1_enumset1 @ X37 @ X36 @ X35)))),
% 1.97/2.17      inference('simplify', [status(thm)], ['13'])).
% 1.97/2.17  thf('15', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.97/2.17          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.97/2.17      inference('sup-', [status(thm)], ['12', '14'])).
% 1.97/2.17  thf('16', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.97/2.17          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.97/2.17      inference('sup-', [status(thm)], ['11', '15'])).
% 1.97/2.17  thf('17', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.97/2.17          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.97/2.17      inference('sup-', [status(thm)], ['10', '16'])).
% 1.97/2.17  thf('18', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.97/2.17          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.97/2.17          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.97/2.17          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.97/2.17      inference('sup-', [status(thm)], ['9', '17'])).
% 1.97/2.17  thf('19', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.97/2.17          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.97/2.17      inference('simplify', [status(thm)], ['18'])).
% 1.97/2.17  thf('20', plain,
% 1.97/2.17      (![X10 : $i, X11 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X11))),
% 1.97/2.17      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.97/2.17  thf('21', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         ((r2_hidden @ X0 @ X1)
% 1.97/2.17          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.97/2.17          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.97/2.17      inference('sup+', [status(thm)], ['19', '20'])).
% 1.97/2.17  thf('22', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.97/2.17      inference('simplify', [status(thm)], ['21'])).
% 1.97/2.17  thf(t45_zfmisc_1, conjecture,
% 1.97/2.17    (![A:$i,B:$i]:
% 1.97/2.17     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.97/2.17       ( r2_hidden @ A @ B ) ))).
% 1.97/2.17  thf(zf_stmt_3, negated_conjecture,
% 1.97/2.17    (~( ![A:$i,B:$i]:
% 1.97/2.17        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.97/2.17          ( r2_hidden @ A @ B ) ) )),
% 1.97/2.17    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 1.97/2.17  thf('23', plain,
% 1.97/2.17      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 1.97/2.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.97/2.17  thf(d10_xboole_0, axiom,
% 1.97/2.17    (![A:$i,B:$i]:
% 1.97/2.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.97/2.17  thf('24', plain,
% 1.97/2.17      (![X14 : $i, X16 : $i]:
% 1.97/2.17         (((X14) = (X16))
% 1.97/2.17          | ~ (r1_tarski @ X16 @ X14)
% 1.97/2.17          | ~ (r1_tarski @ X14 @ X16))),
% 1.97/2.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.97/2.17  thf('25', plain,
% 1.97/2.17      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 1.97/2.17        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.97/2.17      inference('sup-', [status(thm)], ['23', '24'])).
% 1.97/2.17  thf(commutativity_k2_tarski, axiom,
% 1.97/2.17    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.97/2.17  thf('26', plain,
% 1.97/2.17      (![X27 : $i, X28 : $i]:
% 1.97/2.17         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 1.97/2.17      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.97/2.17  thf(l51_zfmisc_1, axiom,
% 1.97/2.17    (![A:$i,B:$i]:
% 1.97/2.17     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.97/2.17  thf('27', plain,
% 1.97/2.17      (![X51 : $i, X52 : $i]:
% 1.97/2.17         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 1.97/2.17      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.97/2.17  thf('28', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.97/2.17      inference('sup+', [status(thm)], ['26', '27'])).
% 1.97/2.17  thf('29', plain,
% 1.97/2.17      (![X51 : $i, X52 : $i]:
% 1.97/2.17         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 1.97/2.17      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.97/2.17  thf('30', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.97/2.17      inference('sup+', [status(thm)], ['28', '29'])).
% 1.97/2.17  thf(t7_xboole_1, axiom,
% 1.97/2.17    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.97/2.17  thf('31', plain,
% 1.97/2.17      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 1.97/2.17      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.97/2.17  thf('32', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.97/2.17      inference('sup+', [status(thm)], ['28', '29'])).
% 1.97/2.17  thf('33', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.97/2.17      inference('demod', [status(thm)], ['25', '30', '31', '32'])).
% 1.97/2.17  thf(t70_xboole_1, axiom,
% 1.97/2.17    (![A:$i,B:$i,C:$i]:
% 1.97/2.17     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.97/2.17            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.97/2.17       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.97/2.17            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.97/2.17  thf('34', plain,
% 1.97/2.17      (![X19 : $i, X20 : $i, X22 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ X19 @ X22)
% 1.97/2.17          | ~ (r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X22)))),
% 1.97/2.17      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.97/2.17  thf('35', plain,
% 1.97/2.17      (![X0 : $i]:
% 1.97/2.17         (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.97/2.17      inference('sup-', [status(thm)], ['33', '34'])).
% 1.97/2.17  thf('36', plain,
% 1.97/2.17      (![X0 : $i]:
% 1.97/2.17         ((r2_hidden @ X0 @ sk_B)
% 1.97/2.17          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 1.97/2.17      inference('sup-', [status(thm)], ['22', '35'])).
% 1.97/2.17  thf('37', plain,
% 1.97/2.17      (![X10 : $i, X11 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 1.97/2.17      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.97/2.17  thf('38', plain,
% 1.97/2.17      (![X10 : $i, X11 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 1.97/2.17      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.97/2.17  thf('39', plain,
% 1.97/2.17      (![X10 : $i, X12 : $i, X13 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X12 @ X10)
% 1.97/2.17          | ~ (r2_hidden @ X12 @ X13)
% 1.97/2.17          | ~ (r1_xboole_0 @ X10 @ X13))),
% 1.97/2.17      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.97/2.17  thf('40', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ X0 @ X1)
% 1.97/2.17          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.97/2.17          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.97/2.17      inference('sup-', [status(thm)], ['38', '39'])).
% 1.97/2.17  thf('41', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         ((r1_xboole_0 @ X0 @ X1)
% 1.97/2.17          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.97/2.17          | (r1_xboole_0 @ X0 @ X1))),
% 1.97/2.17      inference('sup-', [status(thm)], ['37', '40'])).
% 1.97/2.17  thf('42', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.97/2.17      inference('simplify', [status(thm)], ['41'])).
% 1.97/2.17  thf('43', plain,
% 1.97/2.17      (![X0 : $i]:
% 1.97/2.17         ((r2_hidden @ sk_A @ sk_B) | (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 1.97/2.17      inference('sup-', [status(thm)], ['36', '42'])).
% 1.97/2.17  thf('44', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.97/2.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.97/2.17  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0)),
% 1.97/2.17      inference('clc', [status(thm)], ['43', '44'])).
% 1.97/2.17  thf(d4_xboole_0, axiom,
% 1.97/2.17    (![A:$i,B:$i,C:$i]:
% 1.97/2.17     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.97/2.17       ( ![D:$i]:
% 1.97/2.17         ( ( r2_hidden @ D @ C ) <=>
% 1.97/2.17           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.97/2.17  thf('46', plain,
% 1.97/2.17      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.97/2.17         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.97/2.17          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.97/2.17          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.97/2.17      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.97/2.17  thf('47', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.97/2.17          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.97/2.17      inference('eq_fact', [status(thm)], ['46'])).
% 1.97/2.17  thf('48', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.97/2.17          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.97/2.17      inference('eq_fact', [status(thm)], ['46'])).
% 1.97/2.17  thf('49', plain,
% 1.97/2.17      (![X10 : $i, X12 : $i, X13 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X12 @ X10)
% 1.97/2.17          | ~ (r2_hidden @ X12 @ X13)
% 1.97/2.17          | ~ (r1_xboole_0 @ X10 @ X13))),
% 1.97/2.17      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.97/2.17  thf('50', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.17         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.97/2.17          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.97/2.17          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X2))),
% 1.97/2.17      inference('sup-', [status(thm)], ['48', '49'])).
% 1.97/2.17  thf('51', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.97/2.17          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.97/2.17          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.97/2.17      inference('sup-', [status(thm)], ['47', '50'])).
% 1.97/2.17  thf('52', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.97/2.17      inference('simplify', [status(thm)], ['51'])).
% 1.97/2.17  thf('53', plain,
% 1.97/2.17      (![X0 : $i]:
% 1.97/2.17         ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.97/2.17      inference('sup-', [status(thm)], ['45', '52'])).
% 1.97/2.17  thf(t100_xboole_1, axiom,
% 1.97/2.17    (![A:$i,B:$i]:
% 1.97/2.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.97/2.17  thf('54', plain,
% 1.97/2.17      (![X17 : $i, X18 : $i]:
% 1.97/2.17         ((k4_xboole_0 @ X17 @ X18)
% 1.97/2.17           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.97/2.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.97/2.17  thf('55', plain,
% 1.97/2.17      (![X0 : $i]:
% 1.97/2.17         ((k4_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 1.97/2.17           = (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.97/2.17      inference('sup+', [status(thm)], ['53', '54'])).
% 1.97/2.17  thf(t1_xboole_0, axiom,
% 1.97/2.17    (![A:$i,B:$i,C:$i]:
% 1.97/2.17     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.97/2.17       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.97/2.17  thf('56', plain,
% 1.97/2.17      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X6 @ X7)
% 1.97/2.17          | ~ (r2_hidden @ X6 @ X8)
% 1.97/2.17          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.97/2.17      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.97/2.17  thf('57', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 1.97/2.17          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A))
% 1.97/2.17          | ~ (r2_hidden @ X1 @ X0))),
% 1.97/2.17      inference('sup-', [status(thm)], ['55', '56'])).
% 1.97/2.17  thf('58', plain,
% 1.97/2.17      (![X0 : $i]:
% 1.97/2.17         ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.97/2.17      inference('sup-', [status(thm)], ['45', '52'])).
% 1.97/2.17  thf('59', plain,
% 1.97/2.17      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X4 @ X3)
% 1.97/2.17          | (r2_hidden @ X4 @ X1)
% 1.97/2.17          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.97/2.17      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.97/2.17  thf('60', plain,
% 1.97/2.17      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.97/2.17         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.97/2.17      inference('simplify', [status(thm)], ['59'])).
% 1.97/2.17  thf('61', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)) | (r2_hidden @ X1 @ X0))),
% 1.97/2.17      inference('sup-', [status(thm)], ['58', '60'])).
% 1.97/2.17  thf('62', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 1.97/2.17      inference('clc', [status(thm)], ['57', '61'])).
% 1.97/2.17  thf('63', plain,
% 1.97/2.17      (![X0 : $i, X1 : $i]:
% 1.97/2.17         (~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)) | (r2_hidden @ X1 @ X0))),
% 1.97/2.17      inference('sup-', [status(thm)], ['58', '60'])).
% 1.97/2.17  thf('64', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A))),
% 1.97/2.17      inference('clc', [status(thm)], ['62', '63'])).
% 1.97/2.17  thf('65', plain, ($false), inference('sup-', [status(thm)], ['8', '64'])).
% 1.97/2.17  
% 1.97/2.17  % SZS output end Refutation
% 1.97/2.17  
% 1.97/2.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
