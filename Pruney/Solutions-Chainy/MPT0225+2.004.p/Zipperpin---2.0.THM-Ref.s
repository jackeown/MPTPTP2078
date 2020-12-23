%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W5xFogxlDB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:45 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 205 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  723 (1664 expanded)
%              Number of equality atoms :   94 ( 225 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X50 ) )
      | ( X49 = X50 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

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

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X24 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['10','22'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('24',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('34',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X24 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
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

thf('39',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X36 )
      | ( X36
       != ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ ( k1_enumset1 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X27 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('58',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['27','56','57'])).

thf('59',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['25','58'])).

thf('60',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['23','59'])).

thf('61',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('63',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['27','56'])).

thf('64',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W5xFogxlDB
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 868 iterations in 0.388s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.70/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.70/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.89  thf(t17_zfmisc_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( A ) != ( B ) ) =>
% 0.70/0.89       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      (![X49 : $i, X50 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X50))
% 0.70/0.89          | ((X49) = (X50)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.70/0.89  thf(t3_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.70/0.89            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.70/0.89       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.70/0.89            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.70/0.89  thf(t4_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.70/0.89            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.70/0.89       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.70/0.89            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.70/0.89          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.70/0.89      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.70/0.89          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (((X1) = (X0))
% 0.70/0.89          | (r1_xboole_0 @ 
% 0.70/0.89             (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ X2))),
% 0.70/0.89      inference('sup-', [status(thm)], ['0', '3'])).
% 0.70/0.89  thf(t66_xboole_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.70/0.89       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (![X24 : $i]: (((X24) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X24 @ X24))),
% 0.70/0.89      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (((X1) = (X0))
% 0.70/0.89          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.70/0.89              = (k1_xboole_0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.70/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.89  thf(t100_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X16 : $i, X17 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X16 @ X17)
% 0.70/0.89           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X0 @ X1)
% 0.70/0.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.70/0.89            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.70/0.89          | ((X1) = (X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['6', '9'])).
% 0.70/0.89  thf(t3_boole, axiom,
% 0.70/0.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.89  thf('11', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.89  thf(t48_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (![X21 : $i, X22 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.70/0.89           = (k3_xboole_0 @ X21 @ X22))),
% 0.70/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['11', '12'])).
% 0.70/0.89  thf(d10_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.89  thf('15', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.70/0.89      inference('simplify', [status(thm)], ['14'])).
% 0.70/0.89  thf(l32_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (![X13 : $i, X15 : $i]:
% 0.70/0.89         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.70/0.89          | ~ (r1_tarski @ X13 @ X15))),
% 0.70/0.89      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.70/0.89  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['13', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X16 : $i, X17 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X16 @ X17)
% 0.70/0.89           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['18', '19'])).
% 0.70/0.89  thf('21', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.89  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['20', '21'])).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.70/0.89            = (k1_tarski @ X0))
% 0.70/0.89          | ((X1) = (X0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['10', '22'])).
% 0.70/0.89  thf(t20_zfmisc_1, conjecture,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.70/0.89         ( k1_tarski @ A ) ) <=>
% 0.70/0.89       ( ( A ) != ( B ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i]:
% 0.70/0.89        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.70/0.89            ( k1_tarski @ A ) ) <=>
% 0.70/0.89          ( ( A ) != ( B ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      ((((sk_A) = (sk_B))
% 0.70/0.89        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89            != (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89          != (k1_tarski @ sk_A)))
% 0.70/0.89         <= (~
% 0.70/0.89             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89                = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('split', [status(esa)], ['24'])).
% 0.70/0.89  thf('26', plain,
% 0.70/0.89      ((((sk_A) != (sk_B))
% 0.70/0.89        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89            = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (~ (((sk_A) = (sk_B))) | 
% 0.70/0.89       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89          = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('split', [status(esa)], ['26'])).
% 0.70/0.89  thf('28', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.70/0.89      inference('split', [status(esa)], ['24'])).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89          = (k1_tarski @ sk_A)))
% 0.70/0.89         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89                = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('split', [status(esa)], ['26'])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.70/0.89          = (k1_tarski @ sk_A)))
% 0.70/0.89         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89                = (k1_tarski @ sk_A))) & 
% 0.70/0.89             (((sk_A) = (sk_B))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['28', '29'])).
% 0.70/0.89  thf('31', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.70/0.89      inference('split', [status(esa)], ['24'])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.70/0.89          = (k1_tarski @ sk_B)))
% 0.70/0.89         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89                = (k1_tarski @ sk_A))) & 
% 0.70/0.89             (((sk_A) = (sk_B))))),
% 0.70/0.89      inference('demod', [status(thm)], ['30', '31'])).
% 0.70/0.89  thf(t79_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.70/0.89  thf('33', plain,
% 0.70/0.89      (![X25 : $i, X26 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X26)),
% 0.70/0.89      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.70/0.89         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89                = (k1_tarski @ sk_A))) & 
% 0.70/0.89             (((sk_A) = (sk_B))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['32', '33'])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      (![X24 : $i]: (((X24) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X24 @ X24))),
% 0.70/0.89      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.70/0.89         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89                = (k1_tarski @ sk_A))) & 
% 0.70/0.89             (((sk_A) = (sk_B))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.70/0.89  thf(t69_enumset1, axiom,
% 0.70/0.89    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.70/0.89  thf('37', plain,
% 0.70/0.89      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.70/0.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.70/0.89  thf(t70_enumset1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.70/0.89  thf('38', plain,
% 0.70/0.89      (![X40 : $i, X41 : $i]:
% 0.70/0.89         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.70/0.89      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.70/0.89  thf(d1_enumset1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.70/0.89       ( ![E:$i]:
% 0.70/0.89         ( ( r2_hidden @ E @ D ) <=>
% 0.70/0.89           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.70/0.89  thf(zf_stmt_2, axiom,
% 0.70/0.89    (![E:$i,C:$i,B:$i,A:$i]:
% 0.70/0.89     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.70/0.89       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_3, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.70/0.89       ( ![E:$i]:
% 0.70/0.89         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.70/0.89  thf('39', plain,
% 0.70/0.89      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.70/0.89         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35)
% 0.70/0.89          | (r2_hidden @ X32 @ X36)
% 0.70/0.89          | ((X36) != (k1_enumset1 @ X35 @ X34 @ X33)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.70/0.89         ((r2_hidden @ X32 @ (k1_enumset1 @ X35 @ X34 @ X33))
% 0.70/0.89          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35))),
% 0.70/0.89      inference('simplify', [status(thm)], ['39'])).
% 0.70/0.89  thf('41', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.70/0.89          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['38', '40'])).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.70/0.89         (((X28) != (X27)) | ~ (zip_tseitin_0 @ X28 @ X29 @ X30 @ X27))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.89  thf('43', plain,
% 0.70/0.89      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.70/0.89         ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X27)),
% 0.70/0.89      inference('simplify', [status(thm)], ['42'])).
% 0.70/0.89  thf('44', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['41', '43'])).
% 0.70/0.89  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['37', '44'])).
% 0.70/0.89  thf('46', plain,
% 0.70/0.89      (((r2_hidden @ sk_B @ k1_xboole_0))
% 0.70/0.89         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89                = (k1_tarski @ sk_A))) & 
% 0.70/0.89             (((sk_A) = (sk_B))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['36', '45'])).
% 0.70/0.89  thf('47', plain,
% 0.70/0.89      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['13', '17'])).
% 0.70/0.89  thf('48', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.70/0.89          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.70/0.89      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.70/0.89          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['48', '49'])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['47', '50'])).
% 0.70/0.89  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf('53', plain,
% 0.70/0.89      (![X25 : $i, X26 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X26)),
% 0.70/0.89      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.70/0.89  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.70/0.89      inference('sup+', [status(thm)], ['52', '53'])).
% 0.70/0.89  thf('55', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.70/0.89      inference('demod', [status(thm)], ['51', '54'])).
% 0.70/0.89  thf('56', plain,
% 0.70/0.89      (~
% 0.70/0.89       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89          = (k1_tarski @ sk_A))) | 
% 0.70/0.89       ~ (((sk_A) = (sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['46', '55'])).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      (~
% 0.70/0.89       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89          = (k1_tarski @ sk_A))) | 
% 0.70/0.89       (((sk_A) = (sk_B)))),
% 0.70/0.89      inference('split', [status(esa)], ['24'])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (~
% 0.70/0.89       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89          = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('sat_resolution*', [status(thm)], ['27', '56', '57'])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.70/0.89         != (k1_tarski @ sk_A))),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['25', '58'])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | ((sk_B) = (sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['23', '59'])).
% 0.70/0.89  thf('61', plain, (((sk_B) = (sk_A))),
% 0.70/0.89      inference('simplify', [status(thm)], ['60'])).
% 0.70/0.89  thf('62', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.70/0.89      inference('split', [status(esa)], ['26'])).
% 0.70/0.89  thf('63', plain, (~ (((sk_A) = (sk_B)))),
% 0.70/0.89      inference('sat_resolution*', [status(thm)], ['27', '56'])).
% 0.70/0.89  thf('64', plain, (((sk_A) != (sk_B))),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.70/0.89  thf('65', plain, ($false),
% 0.70/0.89      inference('simplify_reflect-', [status(thm)], ['61', '64'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.74/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
