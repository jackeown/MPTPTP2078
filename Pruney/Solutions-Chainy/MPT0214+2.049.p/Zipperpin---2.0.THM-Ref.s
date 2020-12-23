%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Nz1Z3wDGn

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:50 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 105 expanded)
%              Number of leaves         :   36 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  747 ( 891 expanded)
%              Number of equality atoms :   70 (  86 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('16',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k6_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k5_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('17',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('19',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('21',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['15','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['11','33'])).

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Nz1Z3wDGn
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 145 iterations in 0.134s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.59  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.36/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.59  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.59  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.36/0.59                                           $i > $i).
% 0.36/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(d1_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.59       ( ![E:$i]:
% 0.36/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.36/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, axiom,
% 0.36/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.36/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.36/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.36/0.59          | ((X9) = (X10))
% 0.36/0.59          | ((X9) = (X11))
% 0.36/0.59          | ((X9) = (X12)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t6_zfmisc_1, conjecture,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.36/0.59       ( ( A ) = ( B ) ) ))).
% 0.36/0.59  thf(zf_stmt_1, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i]:
% 0.36/0.59        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.36/0.59          ( ( A ) = ( B ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.36/0.59  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.59  thf(t28_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i]:
% 0.36/0.59         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.36/0.59         = (k1_tarski @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.59  thf(t100_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.36/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.59  thf(t92_xboole_1, axiom,
% 0.36/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.59  thf('6', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.36/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf(t98_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X6 : $i, X7 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ X6 @ X7)
% 0.36/0.59           = (k5_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.36/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['7', '8'])).
% 0.36/0.59  thf(t5_boole, axiom,
% 0.36/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.59  thf('10', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.36/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.36/0.59         = (k1_tarski @ sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.59  thf(t69_enumset1, axiom,
% 0.36/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.36/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.59  thf(t71_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.59         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.36/0.59           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.36/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.59  thf(t70_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i]:
% 0.36/0.59         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.36/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.59  thf(t75_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.36/0.59     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.36/0.59       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.36/0.59         ((k6_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.36/0.59           = (k5_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.36/0.59      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.36/0.59  thf(t74_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.59     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.59       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.36/0.59         ((k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.36/0.59           = (k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.36/0.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.59         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.59           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf(t73_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.59     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.36/0.59       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.59         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.36/0.59           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.36/0.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.59         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.59           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.59  thf(t72_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.59     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.59         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 0.36/0.59           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 0.36/0.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.59         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.36/0.59         ((k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.36/0.59           = (k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.36/0.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.36/0.59  thf(t68_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.59     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.59       ( k2_xboole_0 @
% 0.36/0.59         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, 
% 0.36/0.59         X27 : $i]:
% 0.36/0.59         ((k6_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.36/0.59           = (k2_xboole_0 @ 
% 0.36/0.59              (k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26) @ 
% 0.36/0.59              (k1_tarski @ X27)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.59         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.36/0.59           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.36/0.59              (k1_tarski @ X6)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['23', '24'])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.59         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.59           = (k2_xboole_0 @ (k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1) @ 
% 0.36/0.59              (k1_tarski @ X0)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['22', '25'])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.59         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.36/0.59           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.36/0.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.59         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 0.36/0.59           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 0.36/0.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.59         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.59           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X3 @ X2 @ X1) @ 
% 0.36/0.59              (k1_tarski @ X0)))),
% 0.36/0.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.36/0.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['15', '29'])).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.36/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['12', '30'])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.59  thf('33', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k2_tarski @ X0 @ X1)
% 0.36/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.59  thf('34', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['11', '33'])).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i]:
% 0.36/0.59         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.36/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.59  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_3, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.59       ( ![E:$i]:
% 0.36/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.36/0.59          | (r2_hidden @ X13 @ X17)
% 0.36/0.59          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.59         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.36/0.59          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.36/0.59      inference('simplify', [status(thm)], ['36'])).
% 0.36/0.59  thf('38', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.36/0.59      inference('sup+', [status(thm)], ['35', '37'])).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.59         (((X9) != (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X10 @ X10 @ X11 @ X8)),
% 0.36/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['38', '40'])).
% 0.36/0.59  thf('42', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.36/0.59      inference('sup+', [status(thm)], ['34', '41'])).
% 0.36/0.59  thf('43', plain,
% 0.36/0.59      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.36/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.59  thf('44', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i]:
% 0.36/0.59         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.36/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.59  thf('45', plain,
% 0.36/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X18 @ X17)
% 0.36/0.59          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.36/0.59          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.36/0.59         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.36/0.59          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['45'])).
% 0.36/0.59  thf('47', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.59          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['44', '46'])).
% 0.36/0.59  thf('48', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.36/0.59          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['43', '47'])).
% 0.36/0.59  thf('49', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.36/0.59      inference('sup-', [status(thm)], ['42', '48'])).
% 0.36/0.59  thf('50', plain,
% 0.36/0.59      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['0', '49'])).
% 0.36/0.59  thf('51', plain, (((sk_A) = (sk_B))),
% 0.36/0.59      inference('simplify', [status(thm)], ['50'])).
% 0.36/0.59  thf('52', plain, (((sk_A) != (sk_B))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.59  thf('53', plain, ($false),
% 0.36/0.59      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
