%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xvP3jsqbgY

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:59 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 131 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  832 (1334 expanded)
%              Number of equality atoms :   73 ( 116 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
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

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
      | ( r2_hidden @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('34',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_B )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','51'])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['30','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('63',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xvP3jsqbgY
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.20  % Solved by: fo/fo7.sh
% 1.00/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.20  % done 1016 iterations in 0.741s
% 1.00/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.20  % SZS output start Refutation
% 1.00/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.00/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.00/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.00/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.20  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.00/1.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.00/1.20  thf(t65_zfmisc_1, conjecture,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.00/1.20       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.00/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.20    (~( ![A:$i,B:$i]:
% 1.00/1.20        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.00/1.20          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.00/1.20    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.00/1.20  thf('0', plain,
% 1.00/1.20      (((r2_hidden @ sk_B @ sk_A)
% 1.00/1.20        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('1', plain,
% 1.00/1.20      (((r2_hidden @ sk_B @ sk_A)) | 
% 1.00/1.20       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.00/1.20      inference('split', [status(esa)], ['0'])).
% 1.00/1.20  thf(t70_enumset1, axiom,
% 1.00/1.20    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.00/1.20  thf('2', plain,
% 1.00/1.20      (![X26 : $i, X27 : $i]:
% 1.00/1.20         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 1.00/1.20      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.00/1.20  thf(d1_enumset1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.00/1.20       ( ![E:$i]:
% 1.00/1.20         ( ( r2_hidden @ E @ D ) <=>
% 1.00/1.20           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.00/1.20  thf(zf_stmt_2, axiom,
% 1.00/1.20    (![E:$i,C:$i,B:$i,A:$i]:
% 1.00/1.20     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.00/1.20       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_3, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.00/1.20       ( ![E:$i]:
% 1.00/1.20         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.00/1.20  thf('3', plain,
% 1.00/1.20      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.00/1.20         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 1.00/1.20          | (r2_hidden @ X18 @ X22)
% 1.00/1.20          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.00/1.20  thf('4', plain,
% 1.00/1.20      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.00/1.20         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 1.00/1.20          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 1.00/1.20      inference('simplify', [status(thm)], ['3'])).
% 1.00/1.20  thf('5', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.00/1.20          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.00/1.20      inference('sup+', [status(thm)], ['2', '4'])).
% 1.00/1.20  thf('6', plain,
% 1.00/1.20      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.00/1.20         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.00/1.20  thf('7', plain,
% 1.00/1.20      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.00/1.20         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 1.00/1.20      inference('simplify', [status(thm)], ['6'])).
% 1.00/1.20  thf('8', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['5', '7'])).
% 1.00/1.20  thf(t69_enumset1, axiom,
% 1.00/1.20    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.00/1.20  thf('9', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.00/1.20      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.00/1.20  thf(d5_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.00/1.20       ( ![D:$i]:
% 1.00/1.20         ( ( r2_hidden @ D @ C ) <=>
% 1.00/1.20           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.00/1.20  thf('10', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.00/1.20         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.00/1.20          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.00/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.20  thf('11', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.00/1.20         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.00/1.20          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.00/1.20          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.00/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.20  thf('12', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.00/1.20          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.00/1.20          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['10', '11'])).
% 1.00/1.20  thf('13', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.00/1.20      inference('simplify', [status(thm)], ['12'])).
% 1.00/1.20  thf('14', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.00/1.20      inference('simplify', [status(thm)], ['12'])).
% 1.00/1.20  thf(l27_zfmisc_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.00/1.20  thf('15', plain,
% 1.00/1.20      (![X31 : $i, X32 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ (k1_tarski @ X31) @ X32) | (r2_hidden @ X31 @ X32))),
% 1.00/1.20      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.00/1.20  thf(symmetry_r1_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.00/1.20  thf('16', plain,
% 1.00/1.20      (![X6 : $i, X7 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 1.00/1.20      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.00/1.20  thf('17', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.00/1.20  thf(t83_xboole_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.00/1.20  thf('18', plain,
% 1.00/1.20      (![X10 : $i, X11 : $i]:
% 1.00/1.20         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 1.00/1.20      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.00/1.20  thf('19', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ X0 @ X1)
% 1.00/1.20          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['17', '18'])).
% 1.00/1.20  thf('20', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X4 @ X3)
% 1.00/1.20          | ~ (r2_hidden @ X4 @ X2)
% 1.00/1.20          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.00/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.20  thf('21', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X4 @ X2)
% 1.00/1.20          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.00/1.20  thf('22', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X2 @ X0)
% 1.00/1.20          | (r2_hidden @ X1 @ X0)
% 1.00/1.20          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['19', '21'])).
% 1.00/1.20  thf('23', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.00/1.20          | (r2_hidden @ X0 @ X2)
% 1.00/1.20          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X2))),
% 1.00/1.20      inference('sup-', [status(thm)], ['14', '22'])).
% 1.00/1.20  thf('24', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.00/1.20          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.00/1.20          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['13', '23'])).
% 1.00/1.20  thf('25', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.00/1.20          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['24'])).
% 1.00/1.20  thf('26', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X4 @ X2)
% 1.00/1.20          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.00/1.20  thf('27', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 1.00/1.20          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.00/1.20          | ~ (r2_hidden @ X2 @ X1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['25', '26'])).
% 1.00/1.20  thf('28', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.00/1.20          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.00/1.20      inference('condensation', [status(thm)], ['27'])).
% 1.00/1.20  thf('29', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 1.00/1.20          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['9', '28'])).
% 1.00/1.20  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['8', '29'])).
% 1.00/1.20  thf('31', plain,
% 1.00/1.20      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.00/1.20      inference('split', [status(esa)], ['0'])).
% 1.00/1.20  thf('32', plain,
% 1.00/1.20      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.00/1.20         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 1.00/1.20          | ((X14) = (X15))
% 1.00/1.20          | ((X14) = (X16))
% 1.00/1.20          | ((X14) = (X17)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.00/1.20  thf('33', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.00/1.20      inference('simplify', [status(thm)], ['12'])).
% 1.00/1.20  thf('34', plain,
% 1.00/1.20      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.00/1.20      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.00/1.20  thf('35', plain,
% 1.00/1.20      (![X26 : $i, X27 : $i]:
% 1.00/1.20         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 1.00/1.20      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.00/1.20  thf('36', plain,
% 1.00/1.20      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X23 @ X22)
% 1.00/1.20          | ~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 1.00/1.20          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.00/1.20  thf('37', plain,
% 1.00/1.20      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.00/1.20         (~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 1.00/1.20          | ~ (r2_hidden @ X23 @ (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['36'])).
% 1.00/1.20  thf('38', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.00/1.20          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['35', '37'])).
% 1.00/1.20  thf('39', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.00/1.20          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['34', '38'])).
% 1.00/1.20  thf('40', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.00/1.20          | ~ (zip_tseitin_0 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X0 @ X0 @ 
% 1.00/1.20               X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '39'])).
% 1.00/1.20  thf('41', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.00/1.20          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.00/1.20          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.00/1.20          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['32', '40'])).
% 1.00/1.20  thf('42', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.00/1.20          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['41'])).
% 1.00/1.20  thf('43', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.00/1.20         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.00/1.20          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.00/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.20  thf('44', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.00/1.20          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.00/1.20      inference('eq_fact', [status(thm)], ['43'])).
% 1.00/1.20  thf('45', plain,
% 1.00/1.20      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.00/1.20        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('46', plain,
% 1.00/1.20      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.00/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.00/1.20      inference('split', [status(esa)], ['45'])).
% 1.00/1.20  thf('47', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X4 @ X2)
% 1.00/1.20          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.00/1.20  thf('48', plain,
% 1.00/1.20      ((![X0 : $i]:
% 1.00/1.20          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.00/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['46', '47'])).
% 1.00/1.20  thf('49', plain,
% 1.00/1.20      ((![X0 : $i]:
% 1.00/1.20          (((k1_tarski @ sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 1.00/1.20           | ~ (r2_hidden @ 
% 1.00/1.20                (sk_D @ (k1_tarski @ sk_B) @ X0 @ (k1_tarski @ sk_B)) @ sk_A)))
% 1.00/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['44', '48'])).
% 1.00/1.20  thf('50', plain,
% 1.00/1.20      (((~ (r2_hidden @ sk_B @ sk_A)
% 1.00/1.20         | ((k1_tarski @ sk_B)
% 1.00/1.20             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 1.00/1.20         | ((k1_tarski @ sk_B)
% 1.00/1.20             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))))
% 1.00/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['42', '49'])).
% 1.00/1.20  thf('51', plain,
% 1.00/1.20      (((((k1_tarski @ sk_B)
% 1.00/1.20           = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 1.00/1.20         | ~ (r2_hidden @ sk_B @ sk_A)))
% 1.00/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.00/1.20      inference('simplify', [status(thm)], ['50'])).
% 1.00/1.20  thf('52', plain,
% 1.00/1.20      ((((k1_tarski @ sk_B)
% 1.00/1.20          = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 1.00/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.00/1.20             ((r2_hidden @ sk_B @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['31', '51'])).
% 1.00/1.20  thf('53', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X4 @ X2)
% 1.00/1.20          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.00/1.20  thf('54', plain,
% 1.00/1.20      ((![X0 : $i]:
% 1.00/1.20          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.00/1.20           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.00/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.00/1.20             ((r2_hidden @ sk_B @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.00/1.20  thf('55', plain,
% 1.00/1.20      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))
% 1.00/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.00/1.20             ((r2_hidden @ sk_B @ sk_A)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['54'])).
% 1.00/1.20  thf('56', plain,
% 1.00/1.20      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.00/1.20       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['30', '55'])).
% 1.00/1.20  thf('57', plain,
% 1.00/1.20      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.00/1.20       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.00/1.20      inference('split', [status(esa)], ['45'])).
% 1.00/1.20  thf('58', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ X0 @ X1)
% 1.00/1.20          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['17', '18'])).
% 1.00/1.20  thf('59', plain,
% 1.00/1.20      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.00/1.20         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.00/1.20      inference('split', [status(esa)], ['0'])).
% 1.00/1.20  thf('60', plain,
% 1.00/1.20      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 1.00/1.20         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['58', '59'])).
% 1.00/1.20  thf('61', plain,
% 1.00/1.20      (((r2_hidden @ sk_B @ sk_A))
% 1.00/1.20         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.00/1.20      inference('simplify', [status(thm)], ['60'])).
% 1.00/1.20  thf('62', plain,
% 1.00/1.20      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.00/1.20      inference('split', [status(esa)], ['45'])).
% 1.00/1.20  thf('63', plain,
% 1.00/1.20      (((r2_hidden @ sk_B @ sk_A)) | 
% 1.00/1.20       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['61', '62'])).
% 1.00/1.20  thf('64', plain, ($false),
% 1.00/1.20      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '63'])).
% 1.00/1.20  
% 1.00/1.20  % SZS output end Refutation
% 1.00/1.20  
% 1.00/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
