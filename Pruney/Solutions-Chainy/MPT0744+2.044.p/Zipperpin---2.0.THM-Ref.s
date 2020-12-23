%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8nCp36DWu8

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:05 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 187 expanded)
%              Number of leaves         :   42 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          : 1092 (1597 expanded)
%              Number of equality atoms :   59 (  73 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( v3_ordinal1 @ X70 )
      | ( r1_ordinal1 @ X71 @ X70 )
      | ( r2_hidden @ X70 @ X71 )
      | ~ ( v3_ordinal1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X63 @ X64 )
      | ( r1_tarski @ X63 @ X64 )
      | ~ ( v1_ordinal1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( v3_ordinal1 @ X70 )
      | ( r1_ordinal1 @ X71 @ X70 )
      | ( r2_hidden @ X70 @ X71 )
      | ~ ( v3_ordinal1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('10',plain,(
    ! [X62: $i] :
      ( ( k1_ordinal1 @ X62 )
      = ( k2_xboole_0 @ X62 @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X62: $i] :
      ( ( k1_ordinal1 @ X62 )
      = ( k3_tarski @ ( k2_tarski @ X62 @ ( k1_tarski @ X62 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( r2_hidden @ X72 @ X73 )
      | ~ ( r1_tarski @ X73 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('20',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( r2_hidden @ X72 @ X73 )
      | ~ ( r1_tarski @ X73 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('26',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( v1_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('29',plain,(
    ! [X61: $i] :
      ( ( v1_ordinal1 @ X61 )
      | ~ ( v3_ordinal1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('30',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','30','31','32'])).

thf('34',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('38',plain,(
    ! [X62: $i] :
      ( ( k1_ordinal1 @ X62 )
      = ( k3_tarski @ ( k2_tarski @ X62 @ ( k1_tarski @ X62 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('46',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
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

thf('47',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      | ( r2_hidden @ X49 @ X58 )
      | ( X58
       != ( k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( r2_hidden @ X49 @ ( k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) )
      | ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X40 != X39 )
      | ~ ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    ! [X39: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ~ ( zip_tseitin_0 @ X39 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','62'])).

thf('64',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('65',plain,(
    ! [X62: $i] :
      ( ( k1_ordinal1 @ X62 )
      = ( k3_tarski @ ( k2_tarski @ X62 @ ( k1_tarski @ X62 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v3_ordinal1 @ X66 )
      | ~ ( v3_ordinal1 @ X67 )
      | ( r1_tarski @ X66 @ X67 )
      | ~ ( r1_ordinal1 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('69',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('73',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ( r2_hidden @ X69 @ X68 )
      | ( X69 = X68 )
      | ( r2_hidden @ X68 @ X69 )
      | ~ ( v3_ordinal1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('74',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( r2_hidden @ X72 @ X73 )
      | ~ ( r1_tarski @ X73 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B_1 = sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( sk_B_1 = sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = sk_A )
        | ( r2_hidden @ sk_A @ ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf('85',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      | ( sk_B_1 = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['66','84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( sk_B_1 = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','89'])).

thf('91',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8nCp36DWu8
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.12/2.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.12/2.31  % Solved by: fo/fo7.sh
% 2.12/2.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.12/2.31  % done 4237 iterations in 1.859s
% 2.12/2.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.12/2.31  % SZS output start Refutation
% 2.12/2.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.12/2.31  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 2.12/2.31  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 2.12/2.31  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.12/2.31  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 2.12/2.31                                               $i > $i > $i > $o).
% 2.12/2.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.12/2.31  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.12/2.31  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 2.12/2.31  thf(sk_A_type, type, sk_A: $i).
% 2.12/2.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.12/2.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.12/2.31  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 2.12/2.31                                           $i > $i).
% 2.12/2.31  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.12/2.31  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 2.12/2.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.12/2.31  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.12/2.31  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 2.12/2.31  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 2.12/2.31  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 2.12/2.31  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.12/2.31  thf(t34_ordinal1, conjecture,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( v3_ordinal1 @ A ) =>
% 2.12/2.31       ( ![B:$i]:
% 2.12/2.31         ( ( v3_ordinal1 @ B ) =>
% 2.12/2.31           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.12/2.31             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 2.12/2.31  thf(zf_stmt_0, negated_conjecture,
% 2.12/2.31    (~( ![A:$i]:
% 2.12/2.31        ( ( v3_ordinal1 @ A ) =>
% 2.12/2.31          ( ![B:$i]:
% 2.12/2.31            ( ( v3_ordinal1 @ B ) =>
% 2.12/2.31              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.12/2.31                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 2.12/2.31    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 2.12/2.31  thf('0', plain,
% 2.12/2.31      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 2.12/2.31        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('1', plain,
% 2.12/2.31      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 2.12/2.31       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.12/2.31      inference('split', [status(esa)], ['0'])).
% 2.12/2.31  thf(t26_ordinal1, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( v3_ordinal1 @ A ) =>
% 2.12/2.31       ( ![B:$i]:
% 2.12/2.31         ( ( v3_ordinal1 @ B ) =>
% 2.12/2.31           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 2.12/2.31  thf('2', plain,
% 2.12/2.31      (![X70 : $i, X71 : $i]:
% 2.12/2.31         (~ (v3_ordinal1 @ X70)
% 2.12/2.31          | (r1_ordinal1 @ X71 @ X70)
% 2.12/2.31          | (r2_hidden @ X70 @ X71)
% 2.12/2.31          | ~ (v3_ordinal1 @ X71))),
% 2.12/2.31      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.12/2.31  thf(d2_ordinal1, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( v1_ordinal1 @ A ) <=>
% 2.12/2.31       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 2.12/2.31  thf('3', plain,
% 2.12/2.31      (![X63 : $i, X64 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X63 @ X64)
% 2.12/2.31          | (r1_tarski @ X63 @ X64)
% 2.12/2.31          | ~ (v1_ordinal1 @ X64))),
% 2.12/2.31      inference('cnf', [status(esa)], [d2_ordinal1])).
% 2.12/2.31  thf('4', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (v3_ordinal1 @ X0)
% 2.12/2.31          | (r1_ordinal1 @ X0 @ X1)
% 2.12/2.31          | ~ (v3_ordinal1 @ X1)
% 2.12/2.31          | ~ (v1_ordinal1 @ X0)
% 2.12/2.31          | (r1_tarski @ X1 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['2', '3'])).
% 2.12/2.31  thf('5', plain,
% 2.12/2.31      (![X70 : $i, X71 : $i]:
% 2.12/2.31         (~ (v3_ordinal1 @ X70)
% 2.12/2.31          | (r1_ordinal1 @ X71 @ X70)
% 2.12/2.31          | (r2_hidden @ X70 @ X71)
% 2.12/2.31          | ~ (v3_ordinal1 @ X71))),
% 2.12/2.31      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.12/2.31  thf(l1_zfmisc_1, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.12/2.31  thf('6', plain,
% 2.12/2.31      (![X34 : $i, X36 : $i]:
% 2.12/2.31         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 2.12/2.31      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.12/2.31  thf('7', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (v3_ordinal1 @ X0)
% 2.12/2.31          | (r1_ordinal1 @ X0 @ X1)
% 2.12/2.31          | ~ (v3_ordinal1 @ X1)
% 2.12/2.31          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['5', '6'])).
% 2.12/2.31  thf('8', plain,
% 2.12/2.31      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 2.12/2.31        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('9', plain,
% 2.12/2.31      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('split', [status(esa)], ['8'])).
% 2.12/2.31  thf(d1_ordinal1, axiom,
% 2.12/2.31    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 2.12/2.31  thf('10', plain,
% 2.12/2.31      (![X62 : $i]:
% 2.12/2.31         ((k1_ordinal1 @ X62) = (k2_xboole_0 @ X62 @ (k1_tarski @ X62)))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.12/2.31  thf(l51_zfmisc_1, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.12/2.31  thf('11', plain,
% 2.12/2.31      (![X37 : $i, X38 : $i]:
% 2.12/2.31         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 2.12/2.31      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.12/2.31  thf('12', plain,
% 2.12/2.31      (![X62 : $i]:
% 2.12/2.31         ((k1_ordinal1 @ X62)
% 2.12/2.31           = (k3_tarski @ (k2_tarski @ X62 @ (k1_tarski @ X62))))),
% 2.12/2.31      inference('demod', [status(thm)], ['10', '11'])).
% 2.12/2.31  thf(d3_xboole_0, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i]:
% 2.12/2.31     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.12/2.31       ( ![D:$i]:
% 2.12/2.31         ( ( r2_hidden @ D @ C ) <=>
% 2.12/2.31           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.12/2.31  thf('13', plain,
% 2.12/2.31      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X4 @ X2)
% 2.12/2.31          | (r2_hidden @ X4 @ X3)
% 2.12/2.31          | (r2_hidden @ X4 @ X1)
% 2.12/2.31          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.12/2.31      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.12/2.31  thf('14', plain,
% 2.12/2.31      (![X1 : $i, X3 : $i, X4 : $i]:
% 2.12/2.31         ((r2_hidden @ X4 @ X1)
% 2.12/2.31          | (r2_hidden @ X4 @ X3)
% 2.12/2.31          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 2.12/2.31      inference('simplify', [status(thm)], ['13'])).
% 2.12/2.31  thf('15', plain,
% 2.12/2.31      (![X37 : $i, X38 : $i]:
% 2.12/2.31         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 2.12/2.31      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.12/2.31  thf('16', plain,
% 2.12/2.31      (![X1 : $i, X3 : $i, X4 : $i]:
% 2.12/2.31         ((r2_hidden @ X4 @ X1)
% 2.12/2.31          | (r2_hidden @ X4 @ X3)
% 2.12/2.31          | ~ (r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X3 @ X1))))),
% 2.12/2.31      inference('demod', [status(thm)], ['14', '15'])).
% 2.12/2.31  thf('17', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 2.12/2.31          | (r2_hidden @ X1 @ X0)
% 2.12/2.31          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['12', '16'])).
% 2.12/2.31  thf('18', plain,
% 2.12/2.31      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31         | (r2_hidden @ sk_A @ sk_B_1)))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['9', '17'])).
% 2.12/2.31  thf(t7_ordinal1, axiom,
% 2.12/2.31    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.12/2.31  thf('19', plain,
% 2.12/2.31      (![X72 : $i, X73 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X72 @ X73) | ~ (r1_tarski @ X73 @ X72))),
% 2.12/2.31      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.12/2.31  thf('20', plain,
% 2.12/2.31      ((((r2_hidden @ sk_A @ sk_B_1)
% 2.12/2.31         | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['18', '19'])).
% 2.12/2.31  thf('21', plain,
% 2.12/2.31      (((~ (v3_ordinal1 @ sk_B_1)
% 2.12/2.31         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 2.12/2.31         | ~ (v3_ordinal1 @ sk_A)
% 2.12/2.31         | (r2_hidden @ sk_A @ sk_B_1)))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['7', '20'])).
% 2.12/2.31  thf('22', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('24', plain,
% 2.12/2.31      ((((r1_ordinal1 @ sk_A @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1)))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('demod', [status(thm)], ['21', '22', '23'])).
% 2.12/2.31  thf('25', plain,
% 2.12/2.31      (![X72 : $i, X73 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X72 @ X73) | ~ (r1_tarski @ X73 @ X72))),
% 2.12/2.31      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.12/2.31  thf('26', plain,
% 2.12/2.31      ((((r1_ordinal1 @ sk_A @ sk_B_1) | ~ (r1_tarski @ sk_B_1 @ sk_A)))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['24', '25'])).
% 2.12/2.31  thf('27', plain,
% 2.12/2.31      (((~ (v1_ordinal1 @ sk_A)
% 2.12/2.31         | ~ (v3_ordinal1 @ sk_B_1)
% 2.12/2.31         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 2.12/2.31         | ~ (v3_ordinal1 @ sk_A)
% 2.12/2.31         | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['4', '26'])).
% 2.12/2.31  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf(cc1_ordinal1, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 2.12/2.31  thf('29', plain,
% 2.12/2.31      (![X61 : $i]: ((v1_ordinal1 @ X61) | ~ (v3_ordinal1 @ X61))),
% 2.12/2.31      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 2.12/2.31  thf('30', plain, ((v1_ordinal1 @ sk_A)),
% 2.12/2.31      inference('sup-', [status(thm)], ['28', '29'])).
% 2.12/2.31  thf('31', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('33', plain,
% 2.12/2.31      ((((r1_ordinal1 @ sk_A @ sk_B_1) | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('demod', [status(thm)], ['27', '30', '31', '32'])).
% 2.12/2.31  thf('34', plain,
% 2.12/2.31      (((r1_ordinal1 @ sk_A @ sk_B_1))
% 2.12/2.31         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('simplify', [status(thm)], ['33'])).
% 2.12/2.31  thf('35', plain,
% 2.12/2.31      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('split', [status(esa)], ['0'])).
% 2.12/2.31  thf('36', plain,
% 2.12/2.31      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 2.12/2.31       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['34', '35'])).
% 2.12/2.31  thf('37', plain,
% 2.12/2.31      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 2.12/2.31       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.12/2.31      inference('split', [status(esa)], ['8'])).
% 2.12/2.31  thf('38', plain,
% 2.12/2.31      (![X62 : $i]:
% 2.12/2.31         ((k1_ordinal1 @ X62)
% 2.12/2.31           = (k3_tarski @ (k2_tarski @ X62 @ (k1_tarski @ X62))))),
% 2.12/2.31      inference('demod', [status(thm)], ['10', '11'])).
% 2.12/2.31  thf(t70_enumset1, axiom,
% 2.12/2.31    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.12/2.31  thf('39', plain,
% 2.12/2.31      (![X7 : $i, X8 : $i]:
% 2.12/2.31         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 2.12/2.31      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.12/2.31  thf(t69_enumset1, axiom,
% 2.12/2.31    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.12/2.31  thf('40', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 2.12/2.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.12/2.31  thf('41', plain,
% 2.12/2.31      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['39', '40'])).
% 2.12/2.31  thf(t71_enumset1, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i]:
% 2.12/2.31     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.12/2.31  thf('42', plain,
% 2.12/2.31      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.12/2.31         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 2.12/2.31      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.12/2.31  thf(t72_enumset1, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i,D:$i]:
% 2.12/2.31     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.12/2.31  thf('43', plain,
% 2.12/2.31      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.12/2.31         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 2.12/2.31           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 2.12/2.31      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.12/2.31  thf(t73_enumset1, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.12/2.31     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 2.12/2.31       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 2.12/2.31  thf('44', plain,
% 2.12/2.31      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.12/2.31         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 2.12/2.31           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 2.12/2.31      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.12/2.31  thf(t74_enumset1, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.12/2.31     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 2.12/2.31       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 2.12/2.31  thf('45', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.12/2.31         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 2.12/2.31           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 2.12/2.31      inference('cnf', [status(esa)], [t74_enumset1])).
% 2.12/2.31  thf(t75_enumset1, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 2.12/2.31     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 2.12/2.31       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 2.12/2.31  thf('46', plain,
% 2.12/2.31      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.12/2.31         ((k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 2.12/2.31           = (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 2.12/2.31      inference('cnf', [status(esa)], [t75_enumset1])).
% 2.12/2.31  thf(d6_enumset1, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 2.12/2.31     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 2.12/2.31       ( ![J:$i]:
% 2.12/2.31         ( ( r2_hidden @ J @ I ) <=>
% 2.12/2.31           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 2.12/2.31                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 2.12/2.31                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 2.12/2.31  thf(zf_stmt_1, type, zip_tseitin_0 :
% 2.12/2.31      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 2.12/2.31  thf(zf_stmt_2, axiom,
% 2.12/2.31    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 2.12/2.31     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 2.12/2.31       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 2.12/2.31         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 2.12/2.31         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 2.12/2.31  thf(zf_stmt_3, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 2.12/2.31     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 2.12/2.31       ( ![J:$i]:
% 2.12/2.31         ( ( r2_hidden @ J @ I ) <=>
% 2.12/2.31           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 2.12/2.31  thf('47', plain,
% 2.12/2.31      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, 
% 2.12/2.31         X56 : $i, X57 : $i, X58 : $i]:
% 2.12/2.31         ((zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 2.12/2.31          | (r2_hidden @ X49 @ X58)
% 2.12/2.31          | ((X58)
% 2.12/2.31              != (k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.12/2.31  thf('48', plain,
% 2.12/2.31      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, 
% 2.12/2.31         X56 : $i, X57 : $i]:
% 2.12/2.31         ((r2_hidden @ X49 @ 
% 2.12/2.31           (k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50))
% 2.12/2.31          | (zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ 
% 2.12/2.31             X57))),
% 2.12/2.31      inference('simplify', [status(thm)], ['47'])).
% 2.12/2.31  thf('49', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.12/2.31         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 2.12/2.31          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 2.12/2.31      inference('sup+', [status(thm)], ['46', '48'])).
% 2.12/2.31  thf('50', plain,
% 2.12/2.31      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 2.12/2.31         X46 : $i, X47 : $i]:
% 2.12/2.31         (((X40) != (X39))
% 2.12/2.31          | ~ (zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ 
% 2.12/2.31               X39))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.12/2.31  thf('51', plain,
% 2.12/2.31      (![X39 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, 
% 2.12/2.31         X47 : $i]:
% 2.12/2.31         ~ (zip_tseitin_0 @ X39 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39)),
% 2.12/2.31      inference('simplify', [status(thm)], ['50'])).
% 2.12/2.31  thf('52', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.12/2.31         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 2.12/2.31      inference('sup-', [status(thm)], ['49', '51'])).
% 2.12/2.31  thf('53', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.12/2.31         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['45', '52'])).
% 2.12/2.31  thf('54', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.12/2.31         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['44', '53'])).
% 2.12/2.31  thf('55', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.12/2.31         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['43', '54'])).
% 2.12/2.31  thf('56', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['42', '55'])).
% 2.12/2.31  thf('57', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['41', '56'])).
% 2.12/2.31  thf('58', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X0 @ X1)
% 2.12/2.31          | (r2_hidden @ X0 @ X2)
% 2.12/2.31          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.12/2.31      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.12/2.31  thf('59', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.12/2.31         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 2.12/2.31      inference('simplify', [status(thm)], ['58'])).
% 2.12/2.31  thf('60', plain,
% 2.12/2.31      (![X37 : $i, X38 : $i]:
% 2.12/2.31         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 2.12/2.31      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.12/2.31  thf('61', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.12/2.31         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 2.12/2.31          | ~ (r2_hidden @ X0 @ X1))),
% 2.12/2.31      inference('demod', [status(thm)], ['59', '60'])).
% 2.12/2.31  thf('62', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['57', '61'])).
% 2.12/2.31  thf('63', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['38', '62'])).
% 2.12/2.31  thf('64', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 2.12/2.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.12/2.31  thf('65', plain,
% 2.12/2.31      (![X62 : $i]:
% 2.12/2.31         ((k1_ordinal1 @ X62)
% 2.12/2.31           = (k3_tarski @ (k2_tarski @ X62 @ (k1_tarski @ X62))))),
% 2.12/2.31      inference('demod', [status(thm)], ['10', '11'])).
% 2.12/2.31  thf('66', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((k1_ordinal1 @ X0)
% 2.12/2.31           = (k3_tarski @ (k2_tarski @ X0 @ (k2_tarski @ X0 @ X0))))),
% 2.12/2.31      inference('sup+', [status(thm)], ['64', '65'])).
% 2.12/2.31  thf('67', plain,
% 2.12/2.31      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('split', [status(esa)], ['8'])).
% 2.12/2.31  thf(redefinition_r1_ordinal1, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 2.12/2.31       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 2.12/2.31  thf('68', plain,
% 2.12/2.31      (![X66 : $i, X67 : $i]:
% 2.12/2.31         (~ (v3_ordinal1 @ X66)
% 2.12/2.31          | ~ (v3_ordinal1 @ X67)
% 2.12/2.31          | (r1_tarski @ X66 @ X67)
% 2.12/2.31          | ~ (r1_ordinal1 @ X66 @ X67))),
% 2.12/2.31      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.12/2.31  thf('69', plain,
% 2.12/2.31      ((((r1_tarski @ sk_A @ sk_B_1)
% 2.12/2.31         | ~ (v3_ordinal1 @ sk_B_1)
% 2.12/2.31         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['67', '68'])).
% 2.12/2.31  thf('70', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('71', plain, ((v3_ordinal1 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('72', plain,
% 2.12/2.31      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.12/2.31  thf(t24_ordinal1, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( v3_ordinal1 @ A ) =>
% 2.12/2.31       ( ![B:$i]:
% 2.12/2.31         ( ( v3_ordinal1 @ B ) =>
% 2.12/2.31           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 2.12/2.31                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 2.12/2.31  thf('73', plain,
% 2.12/2.31      (![X68 : $i, X69 : $i]:
% 2.12/2.31         (~ (v3_ordinal1 @ X68)
% 2.12/2.31          | (r2_hidden @ X69 @ X68)
% 2.12/2.31          | ((X69) = (X68))
% 2.12/2.31          | (r2_hidden @ X68 @ X69)
% 2.12/2.31          | ~ (v3_ordinal1 @ X69))),
% 2.12/2.31      inference('cnf', [status(esa)], [t24_ordinal1])).
% 2.12/2.31  thf('74', plain,
% 2.12/2.31      (![X72 : $i, X73 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X72 @ X73) | ~ (r1_tarski @ X73 @ X72))),
% 2.12/2.31      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.12/2.31  thf('75', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (v3_ordinal1 @ X1)
% 2.12/2.31          | (r2_hidden @ X0 @ X1)
% 2.12/2.31          | ((X1) = (X0))
% 2.12/2.31          | ~ (v3_ordinal1 @ X0)
% 2.12/2.31          | ~ (r1_tarski @ X0 @ X1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['73', '74'])).
% 2.12/2.31  thf('76', plain,
% 2.12/2.31      (((~ (v3_ordinal1 @ sk_A)
% 2.12/2.31         | ((sk_B_1) = (sk_A))
% 2.12/2.31         | (r2_hidden @ sk_A @ sk_B_1)
% 2.12/2.31         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['72', '75'])).
% 2.12/2.31  thf('77', plain, ((v3_ordinal1 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('78', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('79', plain,
% 2.12/2.31      (((((sk_B_1) = (sk_A)) | (r2_hidden @ sk_A @ sk_B_1)))
% 2.12/2.31         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('demod', [status(thm)], ['76', '77', '78'])).
% 2.12/2.31  thf('80', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X0 @ X3)
% 2.12/2.31          | (r2_hidden @ X0 @ X2)
% 2.12/2.31          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.12/2.31      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.12/2.31  thf('81', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.12/2.31         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 2.12/2.31      inference('simplify', [status(thm)], ['80'])).
% 2.12/2.31  thf('82', plain,
% 2.12/2.31      (![X37 : $i, X38 : $i]:
% 2.12/2.31         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 2.12/2.31      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.12/2.31  thf('83', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.12/2.31         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 2.12/2.31          | ~ (r2_hidden @ X0 @ X3))),
% 2.12/2.31      inference('demod', [status(thm)], ['81', '82'])).
% 2.12/2.31  thf('84', plain,
% 2.12/2.31      ((![X0 : $i]:
% 2.12/2.31          (((sk_B_1) = (sk_A))
% 2.12/2.31           | (r2_hidden @ sk_A @ (k3_tarski @ (k2_tarski @ sk_B_1 @ X0)))))
% 2.12/2.31         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['79', '83'])).
% 2.12/2.31  thf('85', plain,
% 2.12/2.31      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)) | ((sk_B_1) = (sk_A))))
% 2.12/2.31         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup+', [status(thm)], ['66', '84'])).
% 2.12/2.31  thf('86', plain,
% 2.12/2.31      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 2.12/2.31         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('split', [status(esa)], ['0'])).
% 2.12/2.31  thf('87', plain,
% 2.12/2.31      ((((sk_B_1) = (sk_A)))
% 2.12/2.31         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 2.12/2.31             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['85', '86'])).
% 2.12/2.31  thf('88', plain,
% 2.12/2.31      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 2.12/2.31         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.12/2.31      inference('split', [status(esa)], ['0'])).
% 2.12/2.31  thf('89', plain,
% 2.12/2.31      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 2.12/2.31         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 2.12/2.31             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['87', '88'])).
% 2.12/2.31  thf('90', plain,
% 2.12/2.31      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 2.12/2.31       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['63', '89'])).
% 2.12/2.31  thf('91', plain, ($false),
% 2.12/2.31      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '90'])).
% 2.12/2.31  
% 2.12/2.31  % SZS output end Refutation
% 2.12/2.31  
% 2.12/2.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
