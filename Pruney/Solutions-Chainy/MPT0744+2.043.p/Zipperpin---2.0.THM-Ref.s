%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wv1ZgxzTkU

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:05 EST 2020

% Result     : Theorem 5.11s
% Output     : Refutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 161 expanded)
%              Number of leaves         :   42 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  953 (1338 expanded)
%              Number of equality atoms :   55 (  60 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X65: $i] :
      ( ( k1_ordinal1 @ X65 )
      = ( k2_xboole_0 @ X65 @ ( k1_tarski @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ ( k3_tarski @ X38 ) )
      | ~ ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('10',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B_1 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X41: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('12',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( r2_hidden @ X66 @ X67 )
      | ( r1_tarski @ X66 @ X67 )
      | ~ ( v1_ordinal1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('14',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('16',plain,(
    ! [X64: $i] :
      ( ( v1_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('17',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ~ ( v3_ordinal1 @ X70 )
      | ( r1_ordinal1 @ X69 @ X70 )
      | ~ ( r1_tarski @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('21',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,(
    ! [X65: $i] :
      ( ( k1_ordinal1 @ X65 )
      = ( k2_xboole_0 @ X65 @ ( k1_tarski @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k5_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('36',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k6_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
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

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      | ( r2_hidden @ X52 @ X61 )
      | ( X61
       != ( k6_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( r2_hidden @ X52 @ ( k6_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 ) )
      | ( zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X43 != X42 )
      | ~ ( zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('41',plain,(
    ! [X42: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ~ ( zip_tseitin_0 @ X42 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X42 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','50'])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X65: $i] :
      ( ( k1_ordinal1 @ X65 )
      = ( k2_xboole_0 @ X65 @ ( k1_tarski @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('56',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ~ ( v3_ordinal1 @ X70 )
      | ( r1_tarski @ X69 @ X70 )
      | ~ ( r1_ordinal1 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('57',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('61',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('62',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('63',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v3_ordinal1 @ X71 )
      | ( r2_hidden @ X72 @ X71 )
      | ~ ( r2_xboole_0 @ X72 @ X71 )
      | ~ ( v1_ordinal1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('64',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X64: $i] :
      ( ( v1_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('67',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B_1 )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      | ( sk_A = sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['54','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','77'])).

thf('79',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wv1ZgxzTkU
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.11/5.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.11/5.29  % Solved by: fo/fo7.sh
% 5.11/5.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.11/5.29  % done 8683 iterations in 4.841s
% 5.11/5.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.11/5.29  % SZS output start Refutation
% 5.11/5.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.11/5.29  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 5.11/5.29  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.11/5.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.11/5.29  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 5.11/5.29  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 5.11/5.29  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 5.11/5.29                                           $i > $i).
% 5.11/5.29  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 5.11/5.29  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 5.11/5.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.11/5.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 5.11/5.29                                               $i > $i > $i > $o).
% 5.11/5.29  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 5.11/5.29  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 5.11/5.29  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 5.11/5.29  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.11/5.29  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 5.11/5.29  thf(sk_A_type, type, sk_A: $i).
% 5.11/5.29  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.11/5.29  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 5.11/5.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.11/5.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.11/5.29  thf(t34_ordinal1, conjecture,
% 5.11/5.29    (![A:$i]:
% 5.11/5.29     ( ( v3_ordinal1 @ A ) =>
% 5.11/5.29       ( ![B:$i]:
% 5.11/5.29         ( ( v3_ordinal1 @ B ) =>
% 5.11/5.29           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 5.11/5.29             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 5.11/5.29  thf(zf_stmt_0, negated_conjecture,
% 5.11/5.29    (~( ![A:$i]:
% 5.11/5.29        ( ( v3_ordinal1 @ A ) =>
% 5.11/5.29          ( ![B:$i]:
% 5.11/5.29            ( ( v3_ordinal1 @ B ) =>
% 5.11/5.29              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 5.11/5.29                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 5.11/5.29    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 5.11/5.29  thf('0', plain,
% 5.11/5.29      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 5.11/5.29        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 5.11/5.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.29  thf('1', plain,
% 5.11/5.29      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 5.11/5.29       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 5.11/5.29      inference('split', [status(esa)], ['0'])).
% 5.11/5.29  thf('2', plain,
% 5.11/5.29      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 5.11/5.29        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 5.11/5.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.29  thf('3', plain,
% 5.11/5.29      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('split', [status(esa)], ['2'])).
% 5.11/5.29  thf(d1_ordinal1, axiom,
% 5.11/5.29    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 5.11/5.29  thf('4', plain,
% 5.11/5.29      (![X65 : $i]:
% 5.11/5.29         ((k1_ordinal1 @ X65) = (k2_xboole_0 @ X65 @ (k1_tarski @ X65)))),
% 5.11/5.29      inference('cnf', [status(esa)], [d1_ordinal1])).
% 5.11/5.29  thf(d3_xboole_0, axiom,
% 5.11/5.29    (![A:$i,B:$i,C:$i]:
% 5.11/5.29     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 5.11/5.29       ( ![D:$i]:
% 5.11/5.29         ( ( r2_hidden @ D @ C ) <=>
% 5.11/5.29           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.11/5.29  thf('5', plain,
% 5.11/5.29      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.11/5.29         (~ (r2_hidden @ X4 @ X2)
% 5.11/5.29          | (r2_hidden @ X4 @ X3)
% 5.11/5.29          | (r2_hidden @ X4 @ X1)
% 5.11/5.29          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 5.11/5.29      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.11/5.29  thf('6', plain,
% 5.11/5.29      (![X1 : $i, X3 : $i, X4 : $i]:
% 5.11/5.29         ((r2_hidden @ X4 @ X1)
% 5.11/5.29          | (r2_hidden @ X4 @ X3)
% 5.11/5.29          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 5.11/5.29      inference('simplify', [status(thm)], ['5'])).
% 5.11/5.29  thf('7', plain,
% 5.11/5.29      (![X0 : $i, X1 : $i]:
% 5.11/5.29         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 5.11/5.29          | (r2_hidden @ X1 @ X0)
% 5.11/5.29          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.11/5.29      inference('sup-', [status(thm)], ['4', '6'])).
% 5.11/5.29  thf('8', plain,
% 5.11/5.29      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 5.11/5.29         | (r2_hidden @ sk_A @ sk_B_1)))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('sup-', [status(thm)], ['3', '7'])).
% 5.11/5.29  thf(l49_zfmisc_1, axiom,
% 5.11/5.29    (![A:$i,B:$i]:
% 5.11/5.29     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 5.11/5.29  thf('9', plain,
% 5.11/5.29      (![X37 : $i, X38 : $i]:
% 5.11/5.29         ((r1_tarski @ X37 @ (k3_tarski @ X38)) | ~ (r2_hidden @ X37 @ X38))),
% 5.11/5.29      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 5.11/5.29  thf('10', plain,
% 5.11/5.29      ((((r2_hidden @ sk_A @ sk_B_1)
% 5.11/5.29         | (r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B_1)))))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('sup-', [status(thm)], ['8', '9'])).
% 5.11/5.29  thf(t31_zfmisc_1, axiom,
% 5.11/5.29    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 5.11/5.29  thf('11', plain, (![X41 : $i]: ((k3_tarski @ (k1_tarski @ X41)) = (X41))),
% 5.11/5.29      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 5.11/5.29  thf('12', plain,
% 5.11/5.29      ((((r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('demod', [status(thm)], ['10', '11'])).
% 5.11/5.29  thf(d2_ordinal1, axiom,
% 5.11/5.29    (![A:$i]:
% 5.11/5.29     ( ( v1_ordinal1 @ A ) <=>
% 5.11/5.29       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 5.11/5.29  thf('13', plain,
% 5.11/5.29      (![X66 : $i, X67 : $i]:
% 5.11/5.29         (~ (r2_hidden @ X66 @ X67)
% 5.11/5.29          | (r1_tarski @ X66 @ X67)
% 5.11/5.29          | ~ (v1_ordinal1 @ X67))),
% 5.11/5.29      inference('cnf', [status(esa)], [d2_ordinal1])).
% 5.11/5.29  thf('14', plain,
% 5.11/5.29      ((((r1_tarski @ sk_A @ sk_B_1)
% 5.11/5.29         | ~ (v1_ordinal1 @ sk_B_1)
% 5.11/5.29         | (r1_tarski @ sk_A @ sk_B_1)))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('sup-', [status(thm)], ['12', '13'])).
% 5.11/5.29  thf('15', plain, ((v3_ordinal1 @ sk_B_1)),
% 5.11/5.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.29  thf(cc1_ordinal1, axiom,
% 5.11/5.29    (![A:$i]:
% 5.11/5.29     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 5.11/5.29  thf('16', plain,
% 5.11/5.29      (![X64 : $i]: ((v1_ordinal1 @ X64) | ~ (v3_ordinal1 @ X64))),
% 5.11/5.29      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 5.11/5.29  thf('17', plain, ((v1_ordinal1 @ sk_B_1)),
% 5.11/5.29      inference('sup-', [status(thm)], ['15', '16'])).
% 5.11/5.29  thf('18', plain,
% 5.11/5.29      ((((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('demod', [status(thm)], ['14', '17'])).
% 5.11/5.29  thf('19', plain,
% 5.11/5.29      (((r1_tarski @ sk_A @ sk_B_1))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('simplify', [status(thm)], ['18'])).
% 5.11/5.29  thf(redefinition_r1_ordinal1, axiom,
% 5.11/5.29    (![A:$i,B:$i]:
% 5.11/5.29     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 5.11/5.29       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 5.11/5.29  thf('20', plain,
% 5.11/5.29      (![X69 : $i, X70 : $i]:
% 5.11/5.29         (~ (v3_ordinal1 @ X69)
% 5.11/5.29          | ~ (v3_ordinal1 @ X70)
% 5.11/5.29          | (r1_ordinal1 @ X69 @ X70)
% 5.11/5.29          | ~ (r1_tarski @ X69 @ X70))),
% 5.11/5.29      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.11/5.29  thf('21', plain,
% 5.11/5.29      ((((r1_ordinal1 @ sk_A @ sk_B_1)
% 5.11/5.29         | ~ (v3_ordinal1 @ sk_B_1)
% 5.11/5.29         | ~ (v3_ordinal1 @ sk_A)))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('sup-', [status(thm)], ['19', '20'])).
% 5.11/5.29  thf('22', plain, ((v3_ordinal1 @ sk_B_1)),
% 5.11/5.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.29  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 5.11/5.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.29  thf('24', plain,
% 5.11/5.29      (((r1_ordinal1 @ sk_A @ sk_B_1))
% 5.11/5.29         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.29      inference('demod', [status(thm)], ['21', '22', '23'])).
% 5.11/5.29  thf('25', plain,
% 5.11/5.29      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.29      inference('split', [status(esa)], ['0'])).
% 5.11/5.29  thf('26', plain,
% 5.11/5.29      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 5.11/5.29       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 5.11/5.29      inference('sup-', [status(thm)], ['24', '25'])).
% 5.11/5.29  thf('27', plain,
% 5.11/5.29      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 5.11/5.29       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 5.11/5.29      inference('split', [status(esa)], ['2'])).
% 5.11/5.29  thf('28', plain,
% 5.11/5.29      (![X65 : $i]:
% 5.11/5.29         ((k1_ordinal1 @ X65) = (k2_xboole_0 @ X65 @ (k1_tarski @ X65)))),
% 5.11/5.29      inference('cnf', [status(esa)], [d1_ordinal1])).
% 5.11/5.29  thf(t70_enumset1, axiom,
% 5.11/5.29    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.11/5.30  thf('29', plain,
% 5.11/5.30      (![X10 : $i, X11 : $i]:
% 5.11/5.30         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 5.11/5.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.11/5.30  thf(t69_enumset1, axiom,
% 5.11/5.30    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.11/5.30  thf('30', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 5.11/5.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.11/5.30  thf('31', plain,
% 5.11/5.30      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 5.11/5.30      inference('sup+', [status(thm)], ['29', '30'])).
% 5.11/5.30  thf(t71_enumset1, axiom,
% 5.11/5.30    (![A:$i,B:$i,C:$i]:
% 5.11/5.30     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.11/5.30  thf('32', plain,
% 5.11/5.30      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.11/5.30         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 5.11/5.30           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 5.11/5.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.11/5.30  thf(t72_enumset1, axiom,
% 5.11/5.30    (![A:$i,B:$i,C:$i,D:$i]:
% 5.11/5.30     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 5.11/5.30  thf('33', plain,
% 5.11/5.30      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 5.11/5.30         ((k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18)
% 5.11/5.30           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 5.11/5.30      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.11/5.30  thf(t73_enumset1, axiom,
% 5.11/5.30    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.11/5.30     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 5.11/5.30       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 5.11/5.30  thf('34', plain,
% 5.11/5.30      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.11/5.30         ((k4_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23)
% 5.11/5.30           = (k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 5.11/5.30      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.11/5.30  thf(t74_enumset1, axiom,
% 5.11/5.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.11/5.30     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 5.11/5.30       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 5.11/5.30  thf('35', plain,
% 5.11/5.30      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 5.11/5.30         ((k5_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 5.11/5.30           = (k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 5.11/5.30      inference('cnf', [status(esa)], [t74_enumset1])).
% 5.11/5.30  thf(t75_enumset1, axiom,
% 5.11/5.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 5.11/5.30     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 5.11/5.30       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 5.11/5.30  thf('36', plain,
% 5.11/5.30      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 5.11/5.30         ((k6_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 5.11/5.30           = (k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 5.11/5.30      inference('cnf', [status(esa)], [t75_enumset1])).
% 5.11/5.30  thf(d6_enumset1, axiom,
% 5.11/5.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 5.11/5.30     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 5.11/5.30       ( ![J:$i]:
% 5.11/5.30         ( ( r2_hidden @ J @ I ) <=>
% 5.11/5.30           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 5.11/5.30                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 5.11/5.30                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 5.11/5.30  thf(zf_stmt_1, type, zip_tseitin_0 :
% 5.11/5.30      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 5.11/5.30  thf(zf_stmt_2, axiom,
% 5.11/5.30    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 5.11/5.30     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 5.11/5.30       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 5.11/5.30         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 5.11/5.30         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 5.11/5.30  thf(zf_stmt_3, axiom,
% 5.11/5.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 5.11/5.30     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 5.11/5.30       ( ![J:$i]:
% 5.11/5.30         ( ( r2_hidden @ J @ I ) <=>
% 5.11/5.30           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 5.11/5.30  thf('37', plain,
% 5.11/5.30      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, 
% 5.11/5.30         X59 : $i, X60 : $i, X61 : $i]:
% 5.11/5.30         ((zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 5.11/5.30          | (r2_hidden @ X52 @ X61)
% 5.11/5.30          | ((X61)
% 5.11/5.30              != (k6_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53)))),
% 5.11/5.30      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.11/5.30  thf('38', plain,
% 5.11/5.30      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, 
% 5.11/5.30         X59 : $i, X60 : $i]:
% 5.11/5.30         ((r2_hidden @ X52 @ 
% 5.11/5.30           (k6_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53))
% 5.11/5.30          | (zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ 
% 5.11/5.30             X60))),
% 5.11/5.30      inference('simplify', [status(thm)], ['37'])).
% 5.11/5.30  thf('39', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 5.11/5.30         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 5.11/5.30          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 5.11/5.30      inference('sup+', [status(thm)], ['36', '38'])).
% 5.11/5.30  thf('40', plain,
% 5.11/5.30      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 5.11/5.30         X49 : $i, X50 : $i]:
% 5.11/5.30         (((X43) != (X42))
% 5.11/5.30          | ~ (zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ 
% 5.11/5.30               X42))),
% 5.11/5.30      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.11/5.30  thf('41', plain,
% 5.11/5.30      (![X42 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, 
% 5.11/5.30         X50 : $i]:
% 5.11/5.30         ~ (zip_tseitin_0 @ X42 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X42)),
% 5.11/5.30      inference('simplify', [status(thm)], ['40'])).
% 5.11/5.30  thf('42', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.11/5.30         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 5.11/5.30      inference('sup-', [status(thm)], ['39', '41'])).
% 5.11/5.30  thf('43', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.11/5.30         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 5.11/5.30      inference('sup+', [status(thm)], ['35', '42'])).
% 5.11/5.30  thf('44', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.11/5.30         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 5.11/5.30      inference('sup+', [status(thm)], ['34', '43'])).
% 5.11/5.30  thf('45', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.11/5.30         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 5.11/5.30      inference('sup+', [status(thm)], ['33', '44'])).
% 5.11/5.30  thf('46', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.30         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.11/5.30      inference('sup+', [status(thm)], ['32', '45'])).
% 5.11/5.30  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.11/5.30      inference('sup+', [status(thm)], ['31', '46'])).
% 5.11/5.30  thf('48', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.11/5.30         (~ (r2_hidden @ X0 @ X1)
% 5.11/5.30          | (r2_hidden @ X0 @ X2)
% 5.11/5.30          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 5.11/5.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.11/5.30  thf('49', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X3 : $i]:
% 5.11/5.30         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 5.11/5.30      inference('simplify', [status(thm)], ['48'])).
% 5.11/5.30  thf('50', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i]:
% 5.11/5.30         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 5.11/5.30      inference('sup-', [status(thm)], ['47', '49'])).
% 5.11/5.30  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 5.11/5.30      inference('sup+', [status(thm)], ['28', '50'])).
% 5.11/5.30  thf('52', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 5.11/5.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.11/5.30  thf('53', plain,
% 5.11/5.30      (![X65 : $i]:
% 5.11/5.30         ((k1_ordinal1 @ X65) = (k2_xboole_0 @ X65 @ (k1_tarski @ X65)))),
% 5.11/5.30      inference('cnf', [status(esa)], [d1_ordinal1])).
% 5.11/5.30  thf('54', plain,
% 5.11/5.30      (![X0 : $i]:
% 5.11/5.30         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 5.11/5.30      inference('sup+', [status(thm)], ['52', '53'])).
% 5.11/5.30  thf('55', plain,
% 5.11/5.30      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('split', [status(esa)], ['2'])).
% 5.11/5.30  thf('56', plain,
% 5.11/5.30      (![X69 : $i, X70 : $i]:
% 5.11/5.30         (~ (v3_ordinal1 @ X69)
% 5.11/5.30          | ~ (v3_ordinal1 @ X70)
% 5.11/5.30          | (r1_tarski @ X69 @ X70)
% 5.11/5.30          | ~ (r1_ordinal1 @ X69 @ X70))),
% 5.11/5.30      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.11/5.30  thf('57', plain,
% 5.11/5.30      ((((r1_tarski @ sk_A @ sk_B_1)
% 5.11/5.30         | ~ (v3_ordinal1 @ sk_B_1)
% 5.11/5.30         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('sup-', [status(thm)], ['55', '56'])).
% 5.11/5.30  thf('58', plain, ((v3_ordinal1 @ sk_B_1)),
% 5.11/5.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.30  thf('59', plain, ((v3_ordinal1 @ sk_A)),
% 5.11/5.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.30  thf('60', plain,
% 5.11/5.30      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('demod', [status(thm)], ['57', '58', '59'])).
% 5.11/5.30  thf(d8_xboole_0, axiom,
% 5.11/5.30    (![A:$i,B:$i]:
% 5.11/5.30     ( ( r2_xboole_0 @ A @ B ) <=>
% 5.11/5.30       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 5.11/5.30  thf('61', plain,
% 5.11/5.30      (![X6 : $i, X8 : $i]:
% 5.11/5.30         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 5.11/5.30      inference('cnf', [status(esa)], [d8_xboole_0])).
% 5.11/5.30  thf('62', plain,
% 5.11/5.30      (((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1)))
% 5.11/5.30         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('sup-', [status(thm)], ['60', '61'])).
% 5.11/5.30  thf(t21_ordinal1, axiom,
% 5.11/5.30    (![A:$i]:
% 5.11/5.30     ( ( v1_ordinal1 @ A ) =>
% 5.11/5.30       ( ![B:$i]:
% 5.11/5.30         ( ( v3_ordinal1 @ B ) =>
% 5.11/5.30           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 5.11/5.30  thf('63', plain,
% 5.11/5.30      (![X71 : $i, X72 : $i]:
% 5.11/5.30         (~ (v3_ordinal1 @ X71)
% 5.11/5.30          | (r2_hidden @ X72 @ X71)
% 5.11/5.30          | ~ (r2_xboole_0 @ X72 @ X71)
% 5.11/5.30          | ~ (v1_ordinal1 @ X72))),
% 5.11/5.30      inference('cnf', [status(esa)], [t21_ordinal1])).
% 5.11/5.30  thf('64', plain,
% 5.11/5.30      (((((sk_A) = (sk_B_1))
% 5.11/5.30         | ~ (v1_ordinal1 @ sk_A)
% 5.11/5.30         | (r2_hidden @ sk_A @ sk_B_1)
% 5.11/5.30         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('sup-', [status(thm)], ['62', '63'])).
% 5.11/5.30  thf('65', plain, ((v3_ordinal1 @ sk_A)),
% 5.11/5.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.30  thf('66', plain,
% 5.11/5.30      (![X64 : $i]: ((v1_ordinal1 @ X64) | ~ (v3_ordinal1 @ X64))),
% 5.11/5.30      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 5.11/5.30  thf('67', plain, ((v1_ordinal1 @ sk_A)),
% 5.11/5.30      inference('sup-', [status(thm)], ['65', '66'])).
% 5.11/5.30  thf('68', plain, ((v3_ordinal1 @ sk_B_1)),
% 5.11/5.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.30  thf('69', plain,
% 5.11/5.30      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1)))
% 5.11/5.30         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('demod', [status(thm)], ['64', '67', '68'])).
% 5.11/5.30  thf('70', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.11/5.30         (~ (r2_hidden @ X0 @ X3)
% 5.11/5.30          | (r2_hidden @ X0 @ X2)
% 5.11/5.30          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 5.11/5.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.11/5.30  thf('71', plain,
% 5.11/5.30      (![X0 : $i, X1 : $i, X3 : $i]:
% 5.11/5.30         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 5.11/5.30      inference('simplify', [status(thm)], ['70'])).
% 5.11/5.30  thf('72', plain,
% 5.11/5.30      ((![X0 : $i]:
% 5.11/5.30          (((sk_A) = (sk_B_1))
% 5.11/5.30           | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0))))
% 5.11/5.30         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('sup-', [status(thm)], ['69', '71'])).
% 5.11/5.30  thf('73', plain,
% 5.11/5.30      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)) | ((sk_A) = (sk_B_1))))
% 5.11/5.30         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('sup+', [status(thm)], ['54', '72'])).
% 5.11/5.30  thf('74', plain,
% 5.11/5.30      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 5.11/5.30         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.30      inference('split', [status(esa)], ['0'])).
% 5.11/5.30  thf('75', plain,
% 5.11/5.30      ((((sk_A) = (sk_B_1)))
% 5.11/5.30         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 5.11/5.30             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('sup-', [status(thm)], ['73', '74'])).
% 5.11/5.30  thf('76', plain,
% 5.11/5.30      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 5.11/5.30         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 5.11/5.30      inference('split', [status(esa)], ['0'])).
% 5.11/5.30  thf('77', plain,
% 5.11/5.30      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 5.11/5.30         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 5.11/5.30             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 5.11/5.30      inference('sup-', [status(thm)], ['75', '76'])).
% 5.11/5.30  thf('78', plain,
% 5.11/5.30      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 5.11/5.30       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 5.11/5.30      inference('sup-', [status(thm)], ['51', '77'])).
% 5.11/5.30  thf('79', plain, ($false),
% 5.11/5.30      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '78'])).
% 5.11/5.30  
% 5.11/5.30  % SZS output end Refutation
% 5.11/5.30  
% 5.11/5.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
