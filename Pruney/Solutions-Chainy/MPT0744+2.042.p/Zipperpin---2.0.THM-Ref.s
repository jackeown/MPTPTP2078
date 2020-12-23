%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Tl7703NAP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:05 EST 2020

% Result     : Theorem 2.68s
% Output     : Refutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 190 expanded)
%              Number of leaves         :   45 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          : 1086 (1575 expanded)
%              Number of equality atoms :   57 (  62 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

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
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ ( k3_tarski @ X39 ) )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('10',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B_1 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X40 @ X41 ) )
      = ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( r2_hidden @ X66 @ X67 )
      | ( r1_tarski @ X66 @ X67 )
      | ~ ( v1_ordinal1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('18',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('20',plain,(
    ! [X64: $i] :
      ( ( v1_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('21',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ( r1_ordinal1 @ X74 @ X73 )
      | ( r2_hidden @ X73 @ X74 )
      | ~ ( v3_ordinal1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_hidden @ X75 @ X76 )
      | ~ ( r1_tarski @ X76 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,(
    ! [X65: $i] :
      ( ( k1_ordinal1 @ X65 )
      = ( k2_xboole_0 @ X65 @ ( k1_tarski @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k6_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
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

thf('43',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      | ( r2_hidden @ X52 @ X61 )
      | ( X61
       != ( k6_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( r2_hidden @ X52 @ ( k6_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 ) )
      | ( zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X43 != X42 )
      | ~ ( zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,(
    ! [X42: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ~ ( zip_tseitin_0 @ X42 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X42 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','56'])).

thf('58',plain,(
    ! [X65: $i] :
      ( ( k1_ordinal1 @ X65 )
      = ( k2_xboole_0 @ X65 @ ( k1_tarski @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('59',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ( r1_ordinal1 @ X74 @ X73 )
      | ( r2_hidden @ X73 @ X74 )
      | ~ ( v3_ordinal1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_ordinal1 @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ~ ( v3_ordinal1 @ X70 )
      | ( r1_tarski @ X69 @ X70 )
      | ~ ( r1_ordinal1 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('70',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ~ ( v3_ordinal1 @ X70 )
      | ( r1_tarski @ X69 @ X70 )
      | ~ ( r1_ordinal1 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('76',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('80',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('81',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('82',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v3_ordinal1 @ X71 )
      | ( r2_hidden @ X72 @ X71 )
      | ~ ( r2_xboole_0 @ X72 @ X71 )
      | ~ ( v1_ordinal1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('83',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X64: $i] :
      ( ( v1_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('86',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','86','87'])).

thf('89',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_hidden @ X75 @ X76 )
      | ~ ( r1_tarski @ X76 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('90',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','90'])).

thf('92',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Tl7703NAP
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:43:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 2.68/2.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.68/2.87  % Solved by: fo/fo7.sh
% 2.68/2.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.68/2.87  % done 4294 iterations in 2.425s
% 2.68/2.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.68/2.87  % SZS output start Refutation
% 2.68/2.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.68/2.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.68/2.87  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 2.68/2.87                                           $i > $i).
% 2.68/2.87  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.68/2.87  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 2.68/2.87  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.68/2.87  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 2.68/2.87  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 2.68/2.87  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 2.68/2.87  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 2.68/2.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.68/2.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 2.68/2.87                                               $i > $i > $i > $o).
% 2.68/2.87  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.68/2.87  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 2.68/2.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.68/2.87  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 2.68/2.87  thf(sk_A_type, type, sk_A: $i).
% 2.68/2.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.68/2.87  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.68/2.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.68/2.87  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 2.68/2.87  thf(t34_ordinal1, conjecture,
% 2.68/2.87    (![A:$i]:
% 2.68/2.87     ( ( v3_ordinal1 @ A ) =>
% 2.68/2.87       ( ![B:$i]:
% 2.68/2.87         ( ( v3_ordinal1 @ B ) =>
% 2.68/2.87           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.68/2.87             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 2.68/2.87  thf(zf_stmt_0, negated_conjecture,
% 2.68/2.87    (~( ![A:$i]:
% 2.68/2.87        ( ( v3_ordinal1 @ A ) =>
% 2.68/2.87          ( ![B:$i]:
% 2.68/2.87            ( ( v3_ordinal1 @ B ) =>
% 2.68/2.87              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.68/2.87                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 2.68/2.87    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 2.68/2.87  thf('0', plain,
% 2.68/2.87      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 2.68/2.87        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('1', plain,
% 2.68/2.87      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 2.68/2.87       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.68/2.87      inference('split', [status(esa)], ['0'])).
% 2.68/2.87  thf('2', plain,
% 2.68/2.87      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 2.68/2.87        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('3', plain,
% 2.68/2.87      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('split', [status(esa)], ['2'])).
% 2.68/2.87  thf(d1_ordinal1, axiom,
% 2.68/2.87    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 2.68/2.87  thf('4', plain,
% 2.68/2.87      (![X65 : $i]:
% 2.68/2.87         ((k1_ordinal1 @ X65) = (k2_xboole_0 @ X65 @ (k1_tarski @ X65)))),
% 2.68/2.87      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.68/2.87  thf(d3_xboole_0, axiom,
% 2.68/2.87    (![A:$i,B:$i,C:$i]:
% 2.68/2.87     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.68/2.87       ( ![D:$i]:
% 2.68/2.87         ( ( r2_hidden @ D @ C ) <=>
% 2.68/2.87           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.68/2.87  thf('5', plain,
% 2.68/2.87      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.68/2.87         (~ (r2_hidden @ X4 @ X2)
% 2.68/2.87          | (r2_hidden @ X4 @ X3)
% 2.68/2.87          | (r2_hidden @ X4 @ X1)
% 2.68/2.87          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.68/2.87      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.68/2.87  thf('6', plain,
% 2.68/2.87      (![X1 : $i, X3 : $i, X4 : $i]:
% 2.68/2.87         ((r2_hidden @ X4 @ X1)
% 2.68/2.87          | (r2_hidden @ X4 @ X3)
% 2.68/2.87          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 2.68/2.87      inference('simplify', [status(thm)], ['5'])).
% 2.68/2.87  thf('7', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i]:
% 2.68/2.87         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 2.68/2.87          | (r2_hidden @ X1 @ X0)
% 2.68/2.87          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['4', '6'])).
% 2.68/2.87  thf('8', plain,
% 2.68/2.87      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 2.68/2.87         | (r2_hidden @ sk_A @ sk_B_1)))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('sup-', [status(thm)], ['3', '7'])).
% 2.68/2.87  thf(l49_zfmisc_1, axiom,
% 2.68/2.87    (![A:$i,B:$i]:
% 2.68/2.87     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 2.68/2.87  thf('9', plain,
% 2.68/2.87      (![X38 : $i, X39 : $i]:
% 2.68/2.87         ((r1_tarski @ X38 @ (k3_tarski @ X39)) | ~ (r2_hidden @ X38 @ X39))),
% 2.68/2.87      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 2.68/2.87  thf('10', plain,
% 2.68/2.87      ((((r2_hidden @ sk_A @ sk_B_1)
% 2.68/2.87         | (r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B_1)))))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('sup-', [status(thm)], ['8', '9'])).
% 2.68/2.87  thf(t69_enumset1, axiom,
% 2.68/2.87    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.68/2.87  thf('11', plain,
% 2.68/2.87      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 2.68/2.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.68/2.87  thf(l51_zfmisc_1, axiom,
% 2.68/2.87    (![A:$i,B:$i]:
% 2.68/2.87     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.68/2.87  thf('12', plain,
% 2.68/2.87      (![X40 : $i, X41 : $i]:
% 2.68/2.87         ((k3_tarski @ (k2_tarski @ X40 @ X41)) = (k2_xboole_0 @ X40 @ X41))),
% 2.68/2.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.68/2.87  thf('13', plain,
% 2.68/2.87      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['11', '12'])).
% 2.68/2.87  thf(idempotence_k2_xboole_0, axiom,
% 2.68/2.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.68/2.87  thf('14', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 2.68/2.87      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.68/2.87  thf('15', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['13', '14'])).
% 2.68/2.87  thf('16', plain,
% 2.68/2.87      ((((r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('demod', [status(thm)], ['10', '15'])).
% 2.68/2.87  thf(d2_ordinal1, axiom,
% 2.68/2.87    (![A:$i]:
% 2.68/2.87     ( ( v1_ordinal1 @ A ) <=>
% 2.68/2.87       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 2.68/2.87  thf('17', plain,
% 2.68/2.87      (![X66 : $i, X67 : $i]:
% 2.68/2.87         (~ (r2_hidden @ X66 @ X67)
% 2.68/2.87          | (r1_tarski @ X66 @ X67)
% 2.68/2.87          | ~ (v1_ordinal1 @ X67))),
% 2.68/2.87      inference('cnf', [status(esa)], [d2_ordinal1])).
% 2.68/2.87  thf('18', plain,
% 2.68/2.87      ((((r1_tarski @ sk_A @ sk_B_1)
% 2.68/2.87         | ~ (v1_ordinal1 @ sk_B_1)
% 2.68/2.87         | (r1_tarski @ sk_A @ sk_B_1)))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('sup-', [status(thm)], ['16', '17'])).
% 2.68/2.87  thf('19', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf(cc1_ordinal1, axiom,
% 2.68/2.87    (![A:$i]:
% 2.68/2.87     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 2.68/2.87  thf('20', plain,
% 2.68/2.87      (![X64 : $i]: ((v1_ordinal1 @ X64) | ~ (v3_ordinal1 @ X64))),
% 2.68/2.87      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 2.68/2.87  thf('21', plain, ((v1_ordinal1 @ sk_B_1)),
% 2.68/2.87      inference('sup-', [status(thm)], ['19', '20'])).
% 2.68/2.87  thf('22', plain,
% 2.68/2.87      ((((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('demod', [status(thm)], ['18', '21'])).
% 2.68/2.87  thf('23', plain,
% 2.68/2.87      (((r1_tarski @ sk_A @ sk_B_1))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('simplify', [status(thm)], ['22'])).
% 2.68/2.87  thf(t26_ordinal1, axiom,
% 2.68/2.87    (![A:$i]:
% 2.68/2.87     ( ( v3_ordinal1 @ A ) =>
% 2.68/2.87       ( ![B:$i]:
% 2.68/2.87         ( ( v3_ordinal1 @ B ) =>
% 2.68/2.87           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 2.68/2.87  thf('24', plain,
% 2.68/2.87      (![X73 : $i, X74 : $i]:
% 2.68/2.87         (~ (v3_ordinal1 @ X73)
% 2.68/2.87          | (r1_ordinal1 @ X74 @ X73)
% 2.68/2.87          | (r2_hidden @ X73 @ X74)
% 2.68/2.87          | ~ (v3_ordinal1 @ X74))),
% 2.68/2.87      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.68/2.87  thf(t7_ordinal1, axiom,
% 2.68/2.87    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.68/2.87  thf('25', plain,
% 2.68/2.87      (![X75 : $i, X76 : $i]:
% 2.68/2.87         (~ (r2_hidden @ X75 @ X76) | ~ (r1_tarski @ X76 @ X75))),
% 2.68/2.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.68/2.87  thf('26', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i]:
% 2.68/2.87         (~ (v3_ordinal1 @ X0)
% 2.68/2.87          | (r1_ordinal1 @ X0 @ X1)
% 2.68/2.87          | ~ (v3_ordinal1 @ X1)
% 2.68/2.87          | ~ (r1_tarski @ X0 @ X1))),
% 2.68/2.87      inference('sup-', [status(thm)], ['24', '25'])).
% 2.68/2.87  thf('27', plain,
% 2.68/2.87      (((~ (v3_ordinal1 @ sk_B_1)
% 2.68/2.87         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 2.68/2.87         | ~ (v3_ordinal1 @ sk_A)))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('sup-', [status(thm)], ['23', '26'])).
% 2.68/2.87  thf('28', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('29', plain, ((v3_ordinal1 @ sk_A)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('30', plain,
% 2.68/2.87      (((r1_ordinal1 @ sk_A @ sk_B_1))
% 2.68/2.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('demod', [status(thm)], ['27', '28', '29'])).
% 2.68/2.87  thf('31', plain,
% 2.68/2.87      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('split', [status(esa)], ['0'])).
% 2.68/2.87  thf('32', plain,
% 2.68/2.87      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 2.68/2.87       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['30', '31'])).
% 2.68/2.87  thf('33', plain,
% 2.68/2.87      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 2.68/2.87       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.68/2.87      inference('split', [status(esa)], ['2'])).
% 2.68/2.87  thf('34', plain,
% 2.68/2.87      (![X65 : $i]:
% 2.68/2.87         ((k1_ordinal1 @ X65) = (k2_xboole_0 @ X65 @ (k1_tarski @ X65)))),
% 2.68/2.87      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.68/2.87  thf(t70_enumset1, axiom,
% 2.68/2.87    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.68/2.87  thf('35', plain,
% 2.68/2.87      (![X11 : $i, X12 : $i]:
% 2.68/2.87         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 2.68/2.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.68/2.87  thf('36', plain,
% 2.68/2.87      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 2.68/2.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.68/2.87  thf('37', plain,
% 2.68/2.87      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['35', '36'])).
% 2.68/2.87  thf(t71_enumset1, axiom,
% 2.68/2.87    (![A:$i,B:$i,C:$i]:
% 2.68/2.87     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.68/2.87  thf('38', plain,
% 2.68/2.87      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.68/2.87         ((k2_enumset1 @ X13 @ X13 @ X14 @ X15)
% 2.68/2.87           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 2.68/2.87      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.68/2.87  thf(t72_enumset1, axiom,
% 2.68/2.87    (![A:$i,B:$i,C:$i,D:$i]:
% 2.68/2.87     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.68/2.87  thf('39', plain,
% 2.68/2.87      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.68/2.87         ((k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19)
% 2.68/2.87           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 2.68/2.87      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.68/2.87  thf(t73_enumset1, axiom,
% 2.68/2.87    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.68/2.87     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 2.68/2.87       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 2.68/2.87  thf('40', plain,
% 2.68/2.87      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.68/2.87         ((k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24)
% 2.68/2.87           = (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 2.68/2.87      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.68/2.87  thf(t74_enumset1, axiom,
% 2.68/2.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.68/2.87     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 2.68/2.87       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 2.68/2.87  thf('41', plain,
% 2.68/2.87      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.68/2.87         ((k5_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 2.68/2.87           = (k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 2.68/2.87      inference('cnf', [status(esa)], [t74_enumset1])).
% 2.68/2.87  thf(t75_enumset1, axiom,
% 2.68/2.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 2.68/2.87     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 2.68/2.87       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 2.68/2.87  thf('42', plain,
% 2.68/2.87      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.68/2.87         ((k6_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 2.68/2.87           = (k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 2.68/2.87      inference('cnf', [status(esa)], [t75_enumset1])).
% 2.68/2.87  thf(d6_enumset1, axiom,
% 2.68/2.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 2.68/2.87     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 2.68/2.87       ( ![J:$i]:
% 2.68/2.87         ( ( r2_hidden @ J @ I ) <=>
% 2.68/2.87           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 2.68/2.87                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 2.68/2.87                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 2.68/2.87  thf(zf_stmt_1, type, zip_tseitin_0 :
% 2.68/2.87      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 2.68/2.87  thf(zf_stmt_2, axiom,
% 2.68/2.87    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 2.68/2.87     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 2.68/2.87       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 2.68/2.87         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 2.68/2.87         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 2.68/2.87  thf(zf_stmt_3, axiom,
% 2.68/2.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 2.68/2.87     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 2.68/2.87       ( ![J:$i]:
% 2.68/2.87         ( ( r2_hidden @ J @ I ) <=>
% 2.68/2.87           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 2.68/2.87  thf('43', plain,
% 2.68/2.87      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, 
% 2.68/2.87         X59 : $i, X60 : $i, X61 : $i]:
% 2.68/2.87         ((zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 2.68/2.87          | (r2_hidden @ X52 @ X61)
% 2.68/2.87          | ((X61)
% 2.68/2.87              != (k6_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53)))),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.68/2.87  thf('44', plain,
% 2.68/2.87      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, 
% 2.68/2.87         X59 : $i, X60 : $i]:
% 2.68/2.87         ((r2_hidden @ X52 @ 
% 2.68/2.87           (k6_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53))
% 2.68/2.87          | (zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ 
% 2.68/2.87             X60))),
% 2.68/2.87      inference('simplify', [status(thm)], ['43'])).
% 2.68/2.87  thf('45', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.68/2.87         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 2.68/2.87          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 2.68/2.87      inference('sup+', [status(thm)], ['42', '44'])).
% 2.68/2.87  thf('46', plain,
% 2.68/2.87      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 2.68/2.87         X49 : $i, X50 : $i]:
% 2.68/2.87         (((X43) != (X42))
% 2.68/2.87          | ~ (zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ 
% 2.68/2.87               X42))),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.68/2.87  thf('47', plain,
% 2.68/2.87      (![X42 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, 
% 2.68/2.87         X50 : $i]:
% 2.68/2.87         ~ (zip_tseitin_0 @ X42 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X42)),
% 2.68/2.87      inference('simplify', [status(thm)], ['46'])).
% 2.68/2.87  thf('48', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.68/2.87         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 2.68/2.87      inference('sup-', [status(thm)], ['45', '47'])).
% 2.68/2.87  thf('49', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.68/2.87         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['41', '48'])).
% 2.68/2.87  thf('50', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.68/2.87         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['40', '49'])).
% 2.68/2.87  thf('51', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.68/2.87         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['39', '50'])).
% 2.68/2.87  thf('52', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.87         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['38', '51'])).
% 2.68/2.87  thf('53', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['37', '52'])).
% 2.68/2.87  thf('54', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.68/2.87         (~ (r2_hidden @ X0 @ X1)
% 2.68/2.87          | (r2_hidden @ X0 @ X2)
% 2.68/2.87          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.68/2.87      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.68/2.87  thf('55', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.68/2.87         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 2.68/2.87      inference('simplify', [status(thm)], ['54'])).
% 2.68/2.87  thf('56', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i]:
% 2.68/2.87         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['53', '55'])).
% 2.68/2.87  thf('57', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['34', '56'])).
% 2.68/2.87  thf('58', plain,
% 2.68/2.87      (![X65 : $i]:
% 2.68/2.87         ((k1_ordinal1 @ X65) = (k2_xboole_0 @ X65 @ (k1_tarski @ X65)))),
% 2.68/2.87      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.68/2.87  thf('59', plain,
% 2.68/2.87      (![X73 : $i, X74 : $i]:
% 2.68/2.87         (~ (v3_ordinal1 @ X73)
% 2.68/2.87          | (r1_ordinal1 @ X74 @ X73)
% 2.68/2.87          | (r2_hidden @ X73 @ X74)
% 2.68/2.87          | ~ (v3_ordinal1 @ X74))),
% 2.68/2.87      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.68/2.87  thf('60', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.68/2.87         (~ (r2_hidden @ X0 @ X3)
% 2.68/2.87          | (r2_hidden @ X0 @ X2)
% 2.68/2.87          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.68/2.87      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.68/2.87  thf('61', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.68/2.87         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 2.68/2.87      inference('simplify', [status(thm)], ['60'])).
% 2.68/2.87  thf('62', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.87         (~ (v3_ordinal1 @ X0)
% 2.68/2.87          | (r1_ordinal1 @ X0 @ X1)
% 2.68/2.87          | ~ (v3_ordinal1 @ X1)
% 2.68/2.87          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['59', '61'])).
% 2.68/2.87  thf('63', plain,
% 2.68/2.87      (![X0 : $i, X1 : $i]:
% 2.68/2.87         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 2.68/2.87          | ~ (v3_ordinal1 @ X1)
% 2.68/2.87          | (r1_ordinal1 @ X0 @ X1)
% 2.68/2.87          | ~ (v3_ordinal1 @ X0))),
% 2.68/2.87      inference('sup+', [status(thm)], ['58', '62'])).
% 2.68/2.87  thf('64', plain,
% 2.68/2.87      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 2.68/2.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('split', [status(esa)], ['0'])).
% 2.68/2.87  thf('65', plain,
% 2.68/2.87      (((~ (v3_ordinal1 @ sk_B_1)
% 2.68/2.87         | (r1_ordinal1 @ sk_B_1 @ sk_A)
% 2.68/2.87         | ~ (v3_ordinal1 @ sk_A)))
% 2.68/2.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('sup-', [status(thm)], ['63', '64'])).
% 2.68/2.87  thf('66', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('68', plain,
% 2.68/2.87      (((r1_ordinal1 @ sk_B_1 @ sk_A))
% 2.68/2.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('demod', [status(thm)], ['65', '66', '67'])).
% 2.68/2.87  thf(redefinition_r1_ordinal1, axiom,
% 2.68/2.87    (![A:$i,B:$i]:
% 2.68/2.87     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 2.68/2.87       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 2.68/2.87  thf('69', plain,
% 2.68/2.87      (![X69 : $i, X70 : $i]:
% 2.68/2.87         (~ (v3_ordinal1 @ X69)
% 2.68/2.87          | ~ (v3_ordinal1 @ X70)
% 2.68/2.87          | (r1_tarski @ X69 @ X70)
% 2.68/2.87          | ~ (r1_ordinal1 @ X69 @ X70))),
% 2.68/2.87      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.68/2.87  thf('70', plain,
% 2.68/2.87      ((((r1_tarski @ sk_B_1 @ sk_A)
% 2.68/2.87         | ~ (v3_ordinal1 @ sk_A)
% 2.68/2.87         | ~ (v3_ordinal1 @ sk_B_1)))
% 2.68/2.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('sup-', [status(thm)], ['68', '69'])).
% 2.68/2.87  thf('71', plain, ((v3_ordinal1 @ sk_A)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('72', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('73', plain,
% 2.68/2.87      (((r1_tarski @ sk_B_1 @ sk_A))
% 2.68/2.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.68/2.87  thf('74', plain,
% 2.68/2.87      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('split', [status(esa)], ['2'])).
% 2.68/2.87  thf('75', plain,
% 2.68/2.87      (![X69 : $i, X70 : $i]:
% 2.68/2.87         (~ (v3_ordinal1 @ X69)
% 2.68/2.87          | ~ (v3_ordinal1 @ X70)
% 2.68/2.87          | (r1_tarski @ X69 @ X70)
% 2.68/2.87          | ~ (r1_ordinal1 @ X69 @ X70))),
% 2.68/2.87      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.68/2.87  thf('76', plain,
% 2.68/2.87      ((((r1_tarski @ sk_A @ sk_B_1)
% 2.68/2.87         | ~ (v3_ordinal1 @ sk_B_1)
% 2.68/2.87         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['74', '75'])).
% 2.68/2.87  thf('77', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('78', plain, ((v3_ordinal1 @ sk_A)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('79', plain,
% 2.68/2.87      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('demod', [status(thm)], ['76', '77', '78'])).
% 2.68/2.87  thf(d8_xboole_0, axiom,
% 2.68/2.87    (![A:$i,B:$i]:
% 2.68/2.87     ( ( r2_xboole_0 @ A @ B ) <=>
% 2.68/2.87       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 2.68/2.87  thf('80', plain,
% 2.68/2.87      (![X6 : $i, X8 : $i]:
% 2.68/2.87         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 2.68/2.87      inference('cnf', [status(esa)], [d8_xboole_0])).
% 2.68/2.87  thf('81', plain,
% 2.68/2.87      (((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1)))
% 2.68/2.87         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['79', '80'])).
% 2.68/2.87  thf(t21_ordinal1, axiom,
% 2.68/2.87    (![A:$i]:
% 2.68/2.87     ( ( v1_ordinal1 @ A ) =>
% 2.68/2.87       ( ![B:$i]:
% 2.68/2.87         ( ( v3_ordinal1 @ B ) =>
% 2.68/2.87           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 2.68/2.87  thf('82', plain,
% 2.68/2.87      (![X71 : $i, X72 : $i]:
% 2.68/2.87         (~ (v3_ordinal1 @ X71)
% 2.68/2.87          | (r2_hidden @ X72 @ X71)
% 2.68/2.87          | ~ (r2_xboole_0 @ X72 @ X71)
% 2.68/2.87          | ~ (v1_ordinal1 @ X72))),
% 2.68/2.87      inference('cnf', [status(esa)], [t21_ordinal1])).
% 2.68/2.87  thf('83', plain,
% 2.68/2.87      (((((sk_A) = (sk_B_1))
% 2.68/2.87         | ~ (v1_ordinal1 @ sk_A)
% 2.68/2.87         | (r2_hidden @ sk_A @ sk_B_1)
% 2.68/2.87         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['81', '82'])).
% 2.68/2.87  thf('84', plain, ((v3_ordinal1 @ sk_A)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('85', plain,
% 2.68/2.87      (![X64 : $i]: ((v1_ordinal1 @ X64) | ~ (v3_ordinal1 @ X64))),
% 2.68/2.87      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 2.68/2.87  thf('86', plain, ((v1_ordinal1 @ sk_A)),
% 2.68/2.87      inference('sup-', [status(thm)], ['84', '85'])).
% 2.68/2.87  thf('87', plain, ((v3_ordinal1 @ sk_B_1)),
% 2.68/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.87  thf('88', plain,
% 2.68/2.87      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1)))
% 2.68/2.87         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('demod', [status(thm)], ['83', '86', '87'])).
% 2.68/2.87  thf('89', plain,
% 2.68/2.87      (![X75 : $i, X76 : $i]:
% 2.68/2.87         (~ (r2_hidden @ X75 @ X76) | ~ (r1_tarski @ X76 @ X75))),
% 2.68/2.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.68/2.87  thf('90', plain,
% 2.68/2.87      (((((sk_A) = (sk_B_1)) | ~ (r1_tarski @ sk_B_1 @ sk_A)))
% 2.68/2.87         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['88', '89'])).
% 2.68/2.87  thf('91', plain,
% 2.68/2.87      ((((sk_A) = (sk_B_1)))
% 2.68/2.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 2.68/2.87             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['73', '90'])).
% 2.68/2.87  thf('92', plain,
% 2.68/2.87      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 2.68/2.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 2.68/2.87      inference('split', [status(esa)], ['0'])).
% 2.68/2.87  thf('93', plain,
% 2.68/2.87      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 2.68/2.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 2.68/2.87             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['91', '92'])).
% 2.68/2.87  thf('94', plain,
% 2.68/2.87      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 2.68/2.87       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 2.68/2.87      inference('sup-', [status(thm)], ['57', '93'])).
% 2.68/2.87  thf('95', plain, ($false),
% 2.68/2.87      inference('sat_resolution*', [status(thm)], ['1', '32', '33', '94'])).
% 2.68/2.87  
% 2.68/2.87  % SZS output end Refutation
% 2.68/2.87  
% 2.68/2.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
