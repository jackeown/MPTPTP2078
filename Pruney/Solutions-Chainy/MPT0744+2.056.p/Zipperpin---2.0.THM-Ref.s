%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2u22qOqFat

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:07 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 206 expanded)
%              Number of leaves         :   37 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          : 1364 (2014 expanded)
%              Number of equality atoms :   85 ( 117 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v3_ordinal1 @ X61 )
      | ~ ( v3_ordinal1 @ X62 )
      | ( r1_ordinal1 @ X61 @ X62 )
      | ( r1_ordinal1 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v3_ordinal1 @ X61 )
      | ~ ( v3_ordinal1 @ X62 )
      | ( r1_ordinal1 @ X61 @ X62 )
      | ( r1_ordinal1 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf('14',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      | ( X40 = X41 )
      | ( X40 = X42 )
      | ( X40 = X43 )
      | ( X40 = X44 )
      | ( X40 = X45 )
      | ( X40 = X46 )
      | ( X40 = X47 )
      | ( X40 = X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('17',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k2_xboole_0 @ X63 @ ( k1_tarski @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X59 @ X58 )
      | ~ ( zip_tseitin_0 @ X59 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      | ( X58
       != ( k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X59: $i] :
      ( ~ ( zip_tseitin_0 @ X59 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      | ~ ( r2_hidden @ X59 @ ( k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','41'])).

thf('43',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','42'])).

thf('44',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('45',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( r2_hidden @ X68 @ X69 )
      | ~ ( r1_tarski @ X69 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('46',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','46'])).

thf('48',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('54',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('59',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('60',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('61',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      | ( r2_hidden @ X49 @ X58 )
      | ( X58
       != ( k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( r2_hidden @ X49 @ ( k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) )
      | ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X40 != X39 )
      | ~ ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X39: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ~ ( zip_tseitin_0 @ X39 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','76'])).

thf('78',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('79',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('82',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('83',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('87',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v3_ordinal1 @ X66 )
      | ( r2_hidden @ X67 @ X66 )
      | ( X67 = X66 )
      | ( r2_hidden @ X66 @ X67 )
      | ~ ( v3_ordinal1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('88',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( r2_hidden @ X68 @ X69 )
      | ~ ( r1_tarski @ X69 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( sk_B = sk_A )
        | ( r2_hidden @ sk_A @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','97'])).

thf('99',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['80','98'])).

thf('100',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','52','53','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2u22qOqFat
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.54/2.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.54/2.73  % Solved by: fo/fo7.sh
% 2.54/2.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.54/2.73  % done 3458 iterations in 2.262s
% 2.54/2.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.54/2.73  % SZS output start Refutation
% 2.54/2.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.54/2.73  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 2.54/2.73  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.54/2.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.54/2.73  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.54/2.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.54/2.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.54/2.73  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 2.54/2.73                                           $i > $i).
% 2.54/2.73  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 2.54/2.73  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 2.54/2.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.54/2.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.54/2.73  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 2.54/2.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 2.54/2.73                                               $i > $i > $i > $o).
% 2.54/2.73  thf(sk_B_type, type, sk_B: $i).
% 2.54/2.73  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 2.54/2.73  thf(sk_A_type, type, sk_A: $i).
% 2.54/2.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.54/2.73  thf(t34_ordinal1, conjecture,
% 2.54/2.73    (![A:$i]:
% 2.54/2.73     ( ( v3_ordinal1 @ A ) =>
% 2.54/2.73       ( ![B:$i]:
% 2.54/2.73         ( ( v3_ordinal1 @ B ) =>
% 2.54/2.73           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.54/2.73             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 2.54/2.73  thf(zf_stmt_0, negated_conjecture,
% 2.54/2.73    (~( ![A:$i]:
% 2.54/2.73        ( ( v3_ordinal1 @ A ) =>
% 2.54/2.73          ( ![B:$i]:
% 2.54/2.73            ( ( v3_ordinal1 @ B ) =>
% 2.54/2.73              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.54/2.73                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 2.54/2.73    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 2.54/2.73  thf('0', plain,
% 2.54/2.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 2.54/2.73        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('1', plain,
% 2.54/2.73      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 2.54/2.73       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.54/2.73      inference('split', [status(esa)], ['0'])).
% 2.54/2.73  thf(connectedness_r1_ordinal1, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 2.54/2.73       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 2.54/2.73  thf('2', plain,
% 2.54/2.73      (![X61 : $i, X62 : $i]:
% 2.54/2.73         (~ (v3_ordinal1 @ X61)
% 2.54/2.73          | ~ (v3_ordinal1 @ X62)
% 2.54/2.73          | (r1_ordinal1 @ X61 @ X62)
% 2.54/2.73          | (r1_ordinal1 @ X62 @ X61))),
% 2.54/2.73      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 2.54/2.73  thf('3', plain,
% 2.54/2.73      (![X0 : $i]:
% 2.54/2.73         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 2.54/2.73      inference('eq_fact', [status(thm)], ['2'])).
% 2.54/2.73  thf('4', plain,
% 2.54/2.73      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 2.54/2.73      inference('simplify', [status(thm)], ['3'])).
% 2.54/2.73  thf('5', plain,
% 2.54/2.73      (![X61 : $i, X62 : $i]:
% 2.54/2.73         (~ (v3_ordinal1 @ X61)
% 2.54/2.73          | ~ (v3_ordinal1 @ X62)
% 2.54/2.73          | (r1_ordinal1 @ X61 @ X62)
% 2.54/2.73          | (r1_ordinal1 @ X62 @ X61))),
% 2.54/2.73      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 2.54/2.73  thf(redefinition_r1_ordinal1, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 2.54/2.73       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 2.54/2.73  thf('6', plain,
% 2.54/2.73      (![X64 : $i, X65 : $i]:
% 2.54/2.73         (~ (v3_ordinal1 @ X64)
% 2.54/2.73          | ~ (v3_ordinal1 @ X65)
% 2.54/2.73          | (r1_tarski @ X64 @ X65)
% 2.54/2.73          | ~ (r1_ordinal1 @ X64 @ X65))),
% 2.54/2.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.54/2.73  thf('7', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i]:
% 2.54/2.73         ((r1_ordinal1 @ X0 @ X1)
% 2.54/2.73          | ~ (v3_ordinal1 @ X0)
% 2.54/2.73          | ~ (v3_ordinal1 @ X1)
% 2.54/2.73          | (r1_tarski @ X1 @ X0)
% 2.54/2.73          | ~ (v3_ordinal1 @ X0)
% 2.54/2.73          | ~ (v3_ordinal1 @ X1))),
% 2.54/2.73      inference('sup-', [status(thm)], ['5', '6'])).
% 2.54/2.73  thf('8', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i]:
% 2.54/2.73         ((r1_tarski @ X1 @ X0)
% 2.54/2.73          | ~ (v3_ordinal1 @ X1)
% 2.54/2.73          | ~ (v3_ordinal1 @ X0)
% 2.54/2.73          | (r1_ordinal1 @ X0 @ X1))),
% 2.54/2.73      inference('simplify', [status(thm)], ['7'])).
% 2.54/2.73  thf('9', plain,
% 2.54/2.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('split', [status(esa)], ['0'])).
% 2.54/2.73  thf('10', plain,
% 2.54/2.73      (((~ (v3_ordinal1 @ sk_A)
% 2.54/2.73         | ~ (v3_ordinal1 @ sk_B)
% 2.54/2.73         | (r1_tarski @ sk_B @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['8', '9'])).
% 2.54/2.73  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('13', plain,
% 2.54/2.73      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('demod', [status(thm)], ['10', '11', '12'])).
% 2.54/2.73  thf(d6_enumset1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 2.54/2.73     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 2.54/2.73       ( ![J:$i]:
% 2.54/2.73         ( ( r2_hidden @ J @ I ) <=>
% 2.54/2.73           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 2.54/2.73                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 2.54/2.73                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 2.54/2.73  thf(zf_stmt_1, axiom,
% 2.54/2.73    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 2.54/2.73     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 2.54/2.73       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 2.54/2.73         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 2.54/2.73         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 2.54/2.73  thf('14', plain,
% 2.54/2.73      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, 
% 2.54/2.73         X47 : $i, X48 : $i]:
% 2.54/2.73         ((zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 2.54/2.73          | ((X40) = (X41))
% 2.54/2.73          | ((X40) = (X42))
% 2.54/2.73          | ((X40) = (X43))
% 2.54/2.73          | ((X40) = (X44))
% 2.54/2.73          | ((X40) = (X45))
% 2.54/2.73          | ((X40) = (X46))
% 2.54/2.73          | ((X40) = (X47))
% 2.54/2.73          | ((X40) = (X48)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.54/2.73  thf('15', plain,
% 2.54/2.73      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('16', plain,
% 2.54/2.73      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 2.54/2.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('split', [status(esa)], ['15'])).
% 2.54/2.73  thf(d1_ordinal1, axiom,
% 2.54/2.73    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 2.54/2.73  thf('17', plain,
% 2.54/2.73      (![X63 : $i]:
% 2.54/2.73         ((k1_ordinal1 @ X63) = (k2_xboole_0 @ X63 @ (k1_tarski @ X63)))),
% 2.54/2.73      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.54/2.73  thf(l51_zfmisc_1, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.54/2.73  thf('18', plain,
% 2.54/2.73      (![X37 : $i, X38 : $i]:
% 2.54/2.73         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 2.54/2.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.54/2.73  thf('19', plain,
% 2.54/2.73      (![X63 : $i]:
% 2.54/2.73         ((k1_ordinal1 @ X63)
% 2.54/2.73           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 2.54/2.73      inference('demod', [status(thm)], ['17', '18'])).
% 2.54/2.73  thf(d3_xboole_0, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.54/2.73       ( ![D:$i]:
% 2.54/2.73         ( ( r2_hidden @ D @ C ) <=>
% 2.54/2.73           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.54/2.73  thf('20', plain,
% 2.54/2.73      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X4 @ X2)
% 2.54/2.73          | (r2_hidden @ X4 @ X3)
% 2.54/2.73          | (r2_hidden @ X4 @ X1)
% 2.54/2.73          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.54/2.73      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.54/2.73  thf('21', plain,
% 2.54/2.73      (![X1 : $i, X3 : $i, X4 : $i]:
% 2.54/2.73         ((r2_hidden @ X4 @ X1)
% 2.54/2.73          | (r2_hidden @ X4 @ X3)
% 2.54/2.73          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 2.54/2.73      inference('simplify', [status(thm)], ['20'])).
% 2.54/2.73  thf('22', plain,
% 2.54/2.73      (![X37 : $i, X38 : $i]:
% 2.54/2.73         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 2.54/2.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.54/2.73  thf('23', plain,
% 2.54/2.73      (![X1 : $i, X3 : $i, X4 : $i]:
% 2.54/2.73         ((r2_hidden @ X4 @ X1)
% 2.54/2.73          | (r2_hidden @ X4 @ X3)
% 2.54/2.73          | ~ (r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X3 @ X1))))),
% 2.54/2.73      inference('demod', [status(thm)], ['21', '22'])).
% 2.54/2.73  thf('24', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 2.54/2.73          | (r2_hidden @ X1 @ X0)
% 2.54/2.73          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['19', '23'])).
% 2.54/2.73  thf('25', plain,
% 2.54/2.73      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 2.54/2.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['16', '24'])).
% 2.54/2.73  thf(t70_enumset1, axiom,
% 2.54/2.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.54/2.73  thf('26', plain,
% 2.54/2.73      (![X7 : $i, X8 : $i]:
% 2.54/2.73         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 2.54/2.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.54/2.73  thf(t69_enumset1, axiom,
% 2.54/2.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.54/2.73  thf('27', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 2.54/2.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.54/2.73  thf('28', plain,
% 2.54/2.73      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.54/2.73      inference('sup+', [status(thm)], ['26', '27'])).
% 2.54/2.73  thf(t71_enumset1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.54/2.73  thf('29', plain,
% 2.54/2.73      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.54/2.73         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 2.54/2.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.54/2.73  thf(t72_enumset1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i]:
% 2.54/2.73     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.54/2.73  thf('30', plain,
% 2.54/2.73      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.54/2.73         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 2.54/2.73           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 2.54/2.73      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.54/2.73  thf(t73_enumset1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.54/2.73     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 2.54/2.73       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 2.54/2.73  thf('31', plain,
% 2.54/2.73      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.54/2.73         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 2.54/2.73           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 2.54/2.73      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.54/2.73  thf(t74_enumset1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.54/2.73     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 2.54/2.73       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 2.54/2.73  thf('32', plain,
% 2.54/2.73      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.54/2.73         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 2.54/2.73           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 2.54/2.73      inference('cnf', [status(esa)], [t74_enumset1])).
% 2.54/2.73  thf(t75_enumset1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 2.54/2.73     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 2.54/2.73       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 2.54/2.73  thf('33', plain,
% 2.54/2.73      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.54/2.73         ((k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 2.54/2.73           = (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 2.54/2.73      inference('cnf', [status(esa)], [t75_enumset1])).
% 2.54/2.73  thf(zf_stmt_2, type, zip_tseitin_0 :
% 2.54/2.73      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 2.54/2.73  thf(zf_stmt_3, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 2.54/2.73     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 2.54/2.73       ( ![J:$i]:
% 2.54/2.73         ( ( r2_hidden @ J @ I ) <=>
% 2.54/2.73           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 2.54/2.73  thf('34', plain,
% 2.54/2.73      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, 
% 2.54/2.73         X57 : $i, X58 : $i, X59 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X59 @ X58)
% 2.54/2.73          | ~ (zip_tseitin_0 @ X59 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ 
% 2.54/2.73               X57)
% 2.54/2.73          | ((X58)
% 2.54/2.73              != (k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.54/2.73  thf('35', plain,
% 2.54/2.73      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, 
% 2.54/2.73         X57 : $i, X59 : $i]:
% 2.54/2.73         (~ (zip_tseitin_0 @ X59 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ 
% 2.54/2.73             X57)
% 2.54/2.73          | ~ (r2_hidden @ X59 @ 
% 2.54/2.73               (k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50)))),
% 2.54/2.73      inference('simplify', [status(thm)], ['34'])).
% 2.54/2.73  thf('36', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 2.54/2.73          | ~ (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 2.54/2.73      inference('sup-', [status(thm)], ['33', '35'])).
% 2.54/2.73  thf('37', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 2.54/2.73          | ~ (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5))),
% 2.54/2.73      inference('sup-', [status(thm)], ['32', '36'])).
% 2.54/2.73  thf('38', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 2.54/2.73          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4))),
% 2.54/2.73      inference('sup-', [status(thm)], ['31', '37'])).
% 2.54/2.73  thf('39', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 2.54/2.73          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 2.54/2.73      inference('sup-', [status(thm)], ['30', '38'])).
% 2.54/2.73  thf('40', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 2.54/2.73          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 2.54/2.73      inference('sup-', [status(thm)], ['29', '39'])).
% 2.54/2.73  thf('41', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.54/2.73          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 2.54/2.73      inference('sup-', [status(thm)], ['28', '40'])).
% 2.54/2.73  thf('42', plain,
% 2.54/2.73      ((((r2_hidden @ sk_A @ sk_B)
% 2.54/2.73         | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ 
% 2.54/2.73              sk_B @ sk_B)))
% 2.54/2.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['25', '41'])).
% 2.54/2.73  thf('43', plain,
% 2.54/2.73      (((((sk_A) = (sk_B))
% 2.54/2.73         | ((sk_A) = (sk_B))
% 2.54/2.73         | ((sk_A) = (sk_B))
% 2.54/2.73         | ((sk_A) = (sk_B))
% 2.54/2.73         | ((sk_A) = (sk_B))
% 2.54/2.73         | ((sk_A) = (sk_B))
% 2.54/2.73         | ((sk_A) = (sk_B))
% 2.54/2.73         | ((sk_A) = (sk_B))
% 2.54/2.73         | (r2_hidden @ sk_A @ sk_B)))
% 2.54/2.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['14', '42'])).
% 2.54/2.73  thf('44', plain,
% 2.54/2.73      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 2.54/2.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('simplify', [status(thm)], ['43'])).
% 2.54/2.73  thf(t7_ordinal1, axiom,
% 2.54/2.73    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.54/2.73  thf('45', plain,
% 2.54/2.73      (![X68 : $i, X69 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X68 @ X69) | ~ (r1_tarski @ X69 @ X68))),
% 2.54/2.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.54/2.73  thf('46', plain,
% 2.54/2.73      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 2.54/2.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['44', '45'])).
% 2.54/2.73  thf('47', plain,
% 2.54/2.73      ((((sk_A) = (sk_B)))
% 2.54/2.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 2.54/2.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['13', '46'])).
% 2.54/2.73  thf('48', plain,
% 2.54/2.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('split', [status(esa)], ['0'])).
% 2.54/2.73  thf('49', plain,
% 2.54/2.73      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 2.54/2.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 2.54/2.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['47', '48'])).
% 2.54/2.73  thf('50', plain,
% 2.54/2.73      ((~ (v3_ordinal1 @ sk_A))
% 2.54/2.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 2.54/2.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['4', '49'])).
% 2.54/2.73  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('52', plain,
% 2.54/2.73      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 2.54/2.73       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.54/2.73      inference('demod', [status(thm)], ['50', '51'])).
% 2.54/2.73  thf('53', plain,
% 2.54/2.73      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 2.54/2.73       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.54/2.73      inference('split', [status(esa)], ['15'])).
% 2.54/2.73  thf('54', plain,
% 2.54/2.73      (![X63 : $i]:
% 2.54/2.73         ((k1_ordinal1 @ X63)
% 2.54/2.73           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 2.54/2.73      inference('demod', [status(thm)], ['17', '18'])).
% 2.54/2.73  thf('55', plain,
% 2.54/2.73      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.54/2.73      inference('sup+', [status(thm)], ['26', '27'])).
% 2.54/2.73  thf('56', plain,
% 2.54/2.73      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.54/2.73         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 2.54/2.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.54/2.73  thf('57', plain,
% 2.54/2.73      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.54/2.73         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 2.54/2.73           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 2.54/2.73      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.54/2.73  thf('58', plain,
% 2.54/2.73      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.54/2.73         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 2.54/2.73           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 2.54/2.73      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.54/2.73  thf('59', plain,
% 2.54/2.73      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.54/2.73         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 2.54/2.73           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 2.54/2.73      inference('cnf', [status(esa)], [t74_enumset1])).
% 2.54/2.73  thf('60', plain,
% 2.54/2.73      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.54/2.73         ((k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 2.54/2.73           = (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 2.54/2.73      inference('cnf', [status(esa)], [t75_enumset1])).
% 2.54/2.73  thf('61', plain,
% 2.54/2.73      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, 
% 2.54/2.73         X56 : $i, X57 : $i, X58 : $i]:
% 2.54/2.73         ((zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 2.54/2.73          | (r2_hidden @ X49 @ X58)
% 2.54/2.73          | ((X58)
% 2.54/2.73              != (k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.54/2.73  thf('62', plain,
% 2.54/2.73      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, 
% 2.54/2.73         X56 : $i, X57 : $i]:
% 2.54/2.73         ((r2_hidden @ X49 @ 
% 2.54/2.73           (k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50))
% 2.54/2.73          | (zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ 
% 2.54/2.73             X57))),
% 2.54/2.73      inference('simplify', [status(thm)], ['61'])).
% 2.54/2.73  thf('63', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.54/2.73         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 2.54/2.73          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 2.54/2.73      inference('sup+', [status(thm)], ['60', '62'])).
% 2.54/2.73  thf('64', plain,
% 2.54/2.73      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 2.54/2.73         X46 : $i, X47 : $i]:
% 2.54/2.73         (((X40) != (X39))
% 2.54/2.73          | ~ (zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ 
% 2.54/2.73               X39))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.54/2.73  thf('65', plain,
% 2.54/2.73      (![X39 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, 
% 2.54/2.73         X47 : $i]:
% 2.54/2.73         ~ (zip_tseitin_0 @ X39 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39)),
% 2.54/2.73      inference('simplify', [status(thm)], ['64'])).
% 2.54/2.73  thf('66', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.54/2.73         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 2.54/2.73      inference('sup-', [status(thm)], ['63', '65'])).
% 2.54/2.73  thf('67', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.54/2.73         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.54/2.73      inference('sup+', [status(thm)], ['59', '66'])).
% 2.54/2.73  thf('68', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.54/2.73         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.54/2.73      inference('sup+', [status(thm)], ['58', '67'])).
% 2.54/2.73  thf('69', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.54/2.73         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.54/2.73      inference('sup+', [status(thm)], ['57', '68'])).
% 2.54/2.73  thf('70', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.73         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.54/2.73      inference('sup+', [status(thm)], ['56', '69'])).
% 2.54/2.73  thf('71', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.54/2.73      inference('sup+', [status(thm)], ['55', '70'])).
% 2.54/2.73  thf('72', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X0 @ X1)
% 2.54/2.73          | (r2_hidden @ X0 @ X2)
% 2.54/2.73          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.54/2.73      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.54/2.73  thf('73', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.54/2.73         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 2.54/2.73      inference('simplify', [status(thm)], ['72'])).
% 2.54/2.73  thf('74', plain,
% 2.54/2.73      (![X37 : $i, X38 : $i]:
% 2.54/2.73         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 2.54/2.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.54/2.73  thf('75', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.54/2.73         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 2.54/2.73          | ~ (r2_hidden @ X0 @ X1))),
% 2.54/2.73      inference('demod', [status(thm)], ['73', '74'])).
% 2.54/2.73  thf('76', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i]:
% 2.54/2.73         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['71', '75'])).
% 2.54/2.73  thf('77', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 2.54/2.73      inference('sup+', [status(thm)], ['54', '76'])).
% 2.54/2.73  thf('78', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 2.54/2.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.54/2.73  thf('79', plain,
% 2.54/2.73      (![X63 : $i]:
% 2.54/2.73         ((k1_ordinal1 @ X63)
% 2.54/2.73           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 2.54/2.73      inference('demod', [status(thm)], ['17', '18'])).
% 2.54/2.73  thf('80', plain,
% 2.54/2.73      (![X0 : $i]:
% 2.54/2.73         ((k1_ordinal1 @ X0)
% 2.54/2.73           = (k3_tarski @ (k2_tarski @ X0 @ (k2_tarski @ X0 @ X0))))),
% 2.54/2.73      inference('sup+', [status(thm)], ['78', '79'])).
% 2.54/2.73  thf('81', plain,
% 2.54/2.73      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('split', [status(esa)], ['15'])).
% 2.54/2.73  thf('82', plain,
% 2.54/2.73      (![X64 : $i, X65 : $i]:
% 2.54/2.73         (~ (v3_ordinal1 @ X64)
% 2.54/2.73          | ~ (v3_ordinal1 @ X65)
% 2.54/2.73          | (r1_tarski @ X64 @ X65)
% 2.54/2.73          | ~ (r1_ordinal1 @ X64 @ X65))),
% 2.54/2.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.54/2.73  thf('83', plain,
% 2.54/2.73      ((((r1_tarski @ sk_A @ sk_B)
% 2.54/2.73         | ~ (v3_ordinal1 @ sk_B)
% 2.54/2.73         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['81', '82'])).
% 2.54/2.73  thf('84', plain, ((v3_ordinal1 @ sk_B)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('85', plain, ((v3_ordinal1 @ sk_A)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('86', plain,
% 2.54/2.73      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('demod', [status(thm)], ['83', '84', '85'])).
% 2.54/2.73  thf(t24_ordinal1, axiom,
% 2.54/2.73    (![A:$i]:
% 2.54/2.73     ( ( v3_ordinal1 @ A ) =>
% 2.54/2.73       ( ![B:$i]:
% 2.54/2.73         ( ( v3_ordinal1 @ B ) =>
% 2.54/2.73           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 2.54/2.73                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 2.54/2.73  thf('87', plain,
% 2.54/2.73      (![X66 : $i, X67 : $i]:
% 2.54/2.73         (~ (v3_ordinal1 @ X66)
% 2.54/2.73          | (r2_hidden @ X67 @ X66)
% 2.54/2.73          | ((X67) = (X66))
% 2.54/2.73          | (r2_hidden @ X66 @ X67)
% 2.54/2.73          | ~ (v3_ordinal1 @ X67))),
% 2.54/2.73      inference('cnf', [status(esa)], [t24_ordinal1])).
% 2.54/2.73  thf('88', plain,
% 2.54/2.73      (![X68 : $i, X69 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X68 @ X69) | ~ (r1_tarski @ X69 @ X68))),
% 2.54/2.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.54/2.73  thf('89', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i]:
% 2.54/2.73         (~ (v3_ordinal1 @ X1)
% 2.54/2.73          | (r2_hidden @ X0 @ X1)
% 2.54/2.73          | ((X1) = (X0))
% 2.54/2.73          | ~ (v3_ordinal1 @ X0)
% 2.54/2.73          | ~ (r1_tarski @ X0 @ X1))),
% 2.54/2.73      inference('sup-', [status(thm)], ['87', '88'])).
% 2.54/2.73  thf('90', plain,
% 2.54/2.73      (((~ (v3_ordinal1 @ sk_A)
% 2.54/2.73         | ((sk_B) = (sk_A))
% 2.54/2.73         | (r2_hidden @ sk_A @ sk_B)
% 2.54/2.73         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['86', '89'])).
% 2.54/2.73  thf('91', plain, ((v3_ordinal1 @ sk_A)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('92', plain, ((v3_ordinal1 @ sk_B)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('93', plain,
% 2.54/2.73      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 2.54/2.73         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('demod', [status(thm)], ['90', '91', '92'])).
% 2.54/2.73  thf('94', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.54/2.73         (~ (r2_hidden @ X0 @ X3)
% 2.54/2.73          | (r2_hidden @ X0 @ X2)
% 2.54/2.73          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.54/2.73      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.54/2.73  thf('95', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.54/2.73         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 2.54/2.73      inference('simplify', [status(thm)], ['94'])).
% 2.54/2.73  thf('96', plain,
% 2.54/2.73      (![X37 : $i, X38 : $i]:
% 2.54/2.73         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 2.54/2.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.54/2.73  thf('97', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.54/2.73         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 2.54/2.73          | ~ (r2_hidden @ X0 @ X3))),
% 2.54/2.73      inference('demod', [status(thm)], ['95', '96'])).
% 2.54/2.73  thf('98', plain,
% 2.54/2.73      ((![X0 : $i]:
% 2.54/2.73          (((sk_B) = (sk_A))
% 2.54/2.73           | (r2_hidden @ sk_A @ (k3_tarski @ (k2_tarski @ sk_B @ X0)))))
% 2.54/2.73         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['93', '97'])).
% 2.54/2.73  thf('99', plain,
% 2.54/2.73      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)) | ((sk_B) = (sk_A))))
% 2.54/2.73         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('sup+', [status(thm)], ['80', '98'])).
% 2.54/2.73  thf('100', plain,
% 2.54/2.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 2.54/2.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('split', [status(esa)], ['0'])).
% 2.54/2.73  thf('101', plain,
% 2.54/2.73      ((((sk_B) = (sk_A)))
% 2.54/2.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 2.54/2.73             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['99', '100'])).
% 2.54/2.73  thf('102', plain,
% 2.54/2.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 2.54/2.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.54/2.73      inference('split', [status(esa)], ['0'])).
% 2.54/2.73  thf('103', plain,
% 2.54/2.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 2.54/2.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 2.54/2.73             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['101', '102'])).
% 2.54/2.73  thf('104', plain,
% 2.54/2.73      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 2.54/2.73       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['77', '103'])).
% 2.54/2.73  thf('105', plain, ($false),
% 2.54/2.73      inference('sat_resolution*', [status(thm)], ['1', '52', '53', '104'])).
% 2.54/2.73  
% 2.54/2.73  % SZS output end Refutation
% 2.54/2.73  
% 2.54/2.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
