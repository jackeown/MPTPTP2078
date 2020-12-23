%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fGfGuA1jum

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:48 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 109 expanded)
%              Number of leaves         :   40 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  801 ( 949 expanded)
%              Number of equality atoms :   72 (  90 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X61: $i,X62: $i] :
      ( r1_tarski @ ( k1_tarski @ X61 ) @ ( k2_tarski @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('23',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k6_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('26',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k6_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k5_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('27',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('29',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('33',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','34'])).

thf('36',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('39',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_A )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','37','38'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X15 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fGfGuA1jum
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.17/1.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.17/1.36  % Solved by: fo/fo7.sh
% 1.17/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.17/1.36  % done 1202 iterations in 0.908s
% 1.17/1.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.17/1.36  % SZS output start Refutation
% 1.17/1.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.17/1.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.17/1.36  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.17/1.36  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.17/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.17/1.36  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.17/1.36  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.17/1.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.17/1.36  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.17/1.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.17/1.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.17/1.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.17/1.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.17/1.36  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.17/1.36                                           $i > $i).
% 1.17/1.36  thf(sk_D_type, type, sk_D: $i).
% 1.17/1.36  thf(sk_C_type, type, sk_C: $i).
% 1.17/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.17/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.17/1.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.17/1.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.17/1.36  thf(d1_enumset1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.17/1.36       ( ![E:$i]:
% 1.17/1.36         ( ( r2_hidden @ E @ D ) <=>
% 1.17/1.36           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.17/1.36  thf(zf_stmt_0, axiom,
% 1.17/1.36    (![E:$i,C:$i,B:$i,A:$i]:
% 1.17/1.36     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.17/1.36       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.17/1.36  thf('0', plain,
% 1.17/1.36      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.17/1.36         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 1.17/1.36          | ((X14) = (X15))
% 1.17/1.36          | ((X14) = (X16))
% 1.17/1.36          | ((X14) = (X17)))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.36  thf(t12_zfmisc_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 1.17/1.36  thf('1', plain,
% 1.17/1.36      (![X61 : $i, X62 : $i]:
% 1.17/1.36         (r1_tarski @ (k1_tarski @ X61) @ (k2_tarski @ X61 @ X62))),
% 1.17/1.36      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.17/1.36  thf(t28_zfmisc_1, conjecture,
% 1.17/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.36     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 1.17/1.36          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 1.17/1.36  thf(zf_stmt_1, negated_conjecture,
% 1.17/1.36    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.36        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 1.17/1.36             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 1.17/1.36    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 1.17/1.36  thf('2', plain,
% 1.17/1.36      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.17/1.36  thf(t28_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.17/1.36  thf('3', plain,
% 1.17/1.36      (![X7 : $i, X8 : $i]:
% 1.17/1.36         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.17/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.17/1.36  thf('4', plain,
% 1.17/1.36      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 1.17/1.36         = (k2_tarski @ sk_A @ sk_B))),
% 1.17/1.36      inference('sup-', [status(thm)], ['2', '3'])).
% 1.17/1.36  thf(commutativity_k3_xboole_0, axiom,
% 1.17/1.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.17/1.36  thf('5', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.17/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.17/1.36  thf(t18_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i]:
% 1.17/1.36     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.17/1.36  thf('6', plain,
% 1.17/1.36      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.17/1.36         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.17/1.36      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.17/1.36  thf('7', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.17/1.36         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.17/1.36      inference('sup-', [status(thm)], ['5', '6'])).
% 1.17/1.36  thf('8', plain,
% 1.17/1.36      (![X0 : $i]:
% 1.17/1.36         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.17/1.36          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D)))),
% 1.17/1.36      inference('sup-', [status(thm)], ['4', '7'])).
% 1.17/1.36  thf('9', plain,
% 1.17/1.36      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 1.17/1.36      inference('sup-', [status(thm)], ['1', '8'])).
% 1.17/1.36  thf('10', plain,
% 1.17/1.36      (![X7 : $i, X8 : $i]:
% 1.17/1.36         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.17/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.17/1.36  thf('11', plain,
% 1.17/1.36      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 1.17/1.36         = (k1_tarski @ sk_A))),
% 1.17/1.36      inference('sup-', [status(thm)], ['9', '10'])).
% 1.17/1.36  thf(t100_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.17/1.36  thf('12', plain,
% 1.17/1.36      (![X2 : $i, X3 : $i]:
% 1.17/1.36         ((k4_xboole_0 @ X2 @ X3)
% 1.17/1.36           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.17/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.17/1.36  thf('13', plain,
% 1.17/1.36      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 1.17/1.36         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.17/1.36      inference('sup+', [status(thm)], ['11', '12'])).
% 1.17/1.36  thf(t92_xboole_1, axiom,
% 1.17/1.36    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.17/1.36  thf('14', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 1.17/1.36      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.17/1.36  thf('15', plain,
% 1.17/1.36      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 1.17/1.36         = (k1_xboole_0))),
% 1.17/1.36      inference('demod', [status(thm)], ['13', '14'])).
% 1.17/1.36  thf(t98_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.17/1.36  thf('16', plain,
% 1.17/1.36      (![X11 : $i, X12 : $i]:
% 1.17/1.36         ((k2_xboole_0 @ X11 @ X12)
% 1.17/1.36           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 1.17/1.36      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.17/1.36  thf('17', plain,
% 1.17/1.36      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_A))
% 1.17/1.36         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ k1_xboole_0))),
% 1.17/1.36      inference('sup+', [status(thm)], ['15', '16'])).
% 1.17/1.36  thf(t5_boole, axiom,
% 1.17/1.36    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.17/1.36  thf('18', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.17/1.36      inference('cnf', [status(esa)], [t5_boole])).
% 1.17/1.36  thf('19', plain,
% 1.17/1.36      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_A))
% 1.17/1.36         = (k2_tarski @ sk_C @ sk_D))),
% 1.17/1.36      inference('demod', [status(thm)], ['17', '18'])).
% 1.17/1.36  thf(t71_enumset1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i]:
% 1.17/1.36     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.17/1.36  thf('20', plain,
% 1.17/1.36      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.17/1.36         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 1.17/1.36           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 1.17/1.36      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.17/1.36  thf(t70_enumset1, axiom,
% 1.17/1.36    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.17/1.36  thf('21', plain,
% 1.17/1.36      (![X34 : $i, X35 : $i]:
% 1.17/1.36         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.17/1.36      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.17/1.36  thf('22', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i]:
% 1.17/1.36         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.17/1.36      inference('sup+', [status(thm)], ['20', '21'])).
% 1.17/1.36  thf(t74_enumset1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.17/1.36     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.17/1.36       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.17/1.36  thf('23', plain,
% 1.17/1.36      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.17/1.36         ((k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 1.17/1.36           = (k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 1.17/1.36      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.17/1.36  thf(t68_enumset1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.17/1.36     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.17/1.36       ( k2_xboole_0 @
% 1.17/1.36         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 1.17/1.36  thf('24', plain,
% 1.17/1.36      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, 
% 1.17/1.36         X32 : $i]:
% 1.17/1.36         ((k6_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 1.17/1.36           = (k2_xboole_0 @ 
% 1.17/1.36              (k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31) @ 
% 1.17/1.36              (k1_tarski @ X32)))),
% 1.17/1.36      inference('cnf', [status(esa)], [t68_enumset1])).
% 1.17/1.36  thf('25', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.17/1.36         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 1.17/1.36           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 1.17/1.36              (k1_tarski @ X6)))),
% 1.17/1.36      inference('sup+', [status(thm)], ['23', '24'])).
% 1.17/1.36  thf(t75_enumset1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.17/1.36     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.17/1.36       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.17/1.36  thf('26', plain,
% 1.17/1.36      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 1.17/1.36         ((k6_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 1.17/1.36           = (k5_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 1.17/1.36      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.17/1.36  thf('27', plain,
% 1.17/1.36      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.17/1.36         ((k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 1.17/1.36           = (k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 1.17/1.36      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.17/1.36  thf('28', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.17/1.36         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.17/1.36           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.17/1.36      inference('sup+', [status(thm)], ['26', '27'])).
% 1.17/1.36  thf(t73_enumset1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.17/1.36     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.17/1.36       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.17/1.36  thf('29', plain,
% 1.17/1.36      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.17/1.36         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.17/1.36           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 1.17/1.36      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.17/1.36  thf('30', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.17/1.36         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.17/1.36           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.17/1.36      inference('sup+', [status(thm)], ['28', '29'])).
% 1.17/1.36  thf('31', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.17/1.36         ((k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 1.17/1.36           (k1_tarski @ X0)) = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.17/1.36      inference('sup+', [status(thm)], ['25', '30'])).
% 1.17/1.36  thf('32', plain,
% 1.17/1.36      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.17/1.36         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.17/1.36           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 1.17/1.36      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.17/1.36  thf(t72_enumset1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.36     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.17/1.36  thf('33', plain,
% 1.17/1.36      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.17/1.36         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 1.17/1.36           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 1.17/1.36      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.17/1.36  thf('34', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.17/1.36         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 1.17/1.36           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.17/1.36      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.17/1.36  thf('35', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.17/1.36         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 1.17/1.36           = (k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2))),
% 1.17/1.36      inference('sup+', [status(thm)], ['22', '34'])).
% 1.17/1.36  thf('36', plain,
% 1.17/1.36      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.17/1.36         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 1.17/1.36           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 1.17/1.36      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.17/1.36  thf('37', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.17/1.36         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 1.17/1.36           = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 1.17/1.36      inference('demod', [status(thm)], ['35', '36'])).
% 1.17/1.36  thf('38', plain,
% 1.17/1.36      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.17/1.36         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 1.17/1.36           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 1.17/1.36      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.17/1.36  thf('39', plain,
% 1.17/1.36      (((k1_enumset1 @ sk_C @ sk_D @ sk_A) = (k2_tarski @ sk_C @ sk_D))),
% 1.17/1.36      inference('demod', [status(thm)], ['19', '37', '38'])).
% 1.17/1.36  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.17/1.36  thf(zf_stmt_3, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.17/1.36       ( ![E:$i]:
% 1.17/1.36         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.17/1.36  thf('40', plain,
% 1.17/1.36      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.17/1.36         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 1.17/1.36          | (r2_hidden @ X18 @ X22)
% 1.17/1.36          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.17/1.36  thf('41', plain,
% 1.17/1.36      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.17/1.36         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 1.17/1.36          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 1.17/1.36      inference('simplify', [status(thm)], ['40'])).
% 1.17/1.36  thf('42', plain,
% 1.17/1.36      (![X0 : $i]:
% 1.17/1.36         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D))
% 1.17/1.36          | (zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C))),
% 1.17/1.36      inference('sup+', [status(thm)], ['39', '41'])).
% 1.17/1.36  thf('43', plain,
% 1.17/1.36      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.17/1.36         (((X14) != (X15)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.36  thf('44', plain,
% 1.17/1.36      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.17/1.36         ~ (zip_tseitin_0 @ X15 @ X15 @ X16 @ X13)),
% 1.17/1.36      inference('simplify', [status(thm)], ['43'])).
% 1.17/1.36  thf('45', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D))),
% 1.17/1.36      inference('sup-', [status(thm)], ['42', '44'])).
% 1.17/1.36  thf('46', plain,
% 1.17/1.36      (![X34 : $i, X35 : $i]:
% 1.17/1.36         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.17/1.36      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.17/1.36  thf('47', plain,
% 1.17/1.36      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.17/1.36         (~ (r2_hidden @ X23 @ X22)
% 1.17/1.36          | ~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 1.17/1.36          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.17/1.36  thf('48', plain,
% 1.17/1.36      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.17/1.36         (~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 1.17/1.36          | ~ (r2_hidden @ X23 @ (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.17/1.36      inference('simplify', [status(thm)], ['47'])).
% 1.17/1.36  thf('49', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.17/1.36         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.17/1.36          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.17/1.36      inference('sup-', [status(thm)], ['46', '48'])).
% 1.17/1.36  thf('50', plain, (~ (zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C)),
% 1.17/1.36      inference('sup-', [status(thm)], ['45', '49'])).
% 1.17/1.36  thf('51', plain,
% 1.17/1.36      ((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_D)))),
% 1.17/1.36      inference('sup-', [status(thm)], ['0', '50'])).
% 1.17/1.36  thf('52', plain, ((((sk_A) = (sk_D)) | ((sk_A) = (sk_C)))),
% 1.17/1.36      inference('simplify', [status(thm)], ['51'])).
% 1.17/1.36  thf('53', plain, (((sk_A) != (sk_C))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.17/1.36  thf('54', plain, (((sk_A) != (sk_D))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.17/1.36  thf('55', plain, ($false),
% 1.17/1.36      inference('simplify_reflect-', [status(thm)], ['52', '53', '54'])).
% 1.17/1.36  
% 1.17/1.36  % SZS output end Refutation
% 1.17/1.36  
% 1.17/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
