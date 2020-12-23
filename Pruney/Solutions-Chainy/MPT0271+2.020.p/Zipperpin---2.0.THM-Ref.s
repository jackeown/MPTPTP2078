%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ABXpa72LiU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:23 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 252 expanded)
%              Number of leaves         :   35 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  981 (1939 expanded)
%              Number of equality atoms :   69 ( 134 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X16 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ X38 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X16 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('24',plain,(
    ! [X27: $i] :
      ( r1_xboole_0 @ X27 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('25',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('45',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('52',plain,(
    ! [X61: $i,X63: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X61 ) @ X63 )
      | ~ ( r2_hidden @ X61 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('53',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('55',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X24 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('61',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf('67',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['43','65','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','67'])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['39','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('71',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['43','65'])).

thf('72',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('75',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X61: $i,X62: $i] :
      ( ( r2_hidden @ X61 @ X62 )
      | ~ ( r1_tarski @ ( k1_tarski @ X61 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('81',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k5_xboole_0 @ X13 @ X15 ) )
      | ( r2_hidden @ X12 @ X15 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','82'])).

thf('84',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('87',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('88',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','94'])).

thf('96',plain,(
    ! [X27: $i] :
      ( r1_xboole_0 @ X27 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ABXpa72LiU
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.87/2.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.87/2.05  % Solved by: fo/fo7.sh
% 1.87/2.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.87/2.05  % done 2286 iterations in 1.595s
% 1.87/2.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.87/2.05  % SZS output start Refutation
% 1.87/2.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.87/2.05  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.87/2.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.87/2.05  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.87/2.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.87/2.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.87/2.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.87/2.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.87/2.05  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.87/2.05  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.87/2.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.87/2.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.87/2.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.87/2.05  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.87/2.05  thf(sk_A_type, type, sk_A: $i).
% 1.87/2.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.87/2.05  thf(sk_B_type, type, sk_B: $i).
% 1.87/2.05  thf(d1_enumset1, axiom,
% 1.87/2.05    (![A:$i,B:$i,C:$i,D:$i]:
% 1.87/2.05     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.87/2.05       ( ![E:$i]:
% 1.87/2.05         ( ( r2_hidden @ E @ D ) <=>
% 1.87/2.05           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.87/2.05  thf(zf_stmt_0, axiom,
% 1.87/2.05    (![E:$i,C:$i,B:$i,A:$i]:
% 1.87/2.05     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.87/2.05       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.87/2.05  thf('0', plain,
% 1.87/2.05      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.87/2.05         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 1.87/2.05          | ((X29) = (X30))
% 1.87/2.05          | ((X29) = (X31))
% 1.87/2.05          | ((X29) = (X32)))),
% 1.87/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.05  thf(t4_xboole_0, axiom,
% 1.87/2.05    (![A:$i,B:$i]:
% 1.87/2.05     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.87/2.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.87/2.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.87/2.05            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.87/2.05  thf('1', plain,
% 1.87/2.05      (![X16 : $i, X17 : $i]:
% 1.87/2.05         ((r1_xboole_0 @ X16 @ X17)
% 1.87/2.05          | (r2_hidden @ (sk_C_1 @ X17 @ X16) @ (k3_xboole_0 @ X16 @ X17)))),
% 1.87/2.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.87/2.05  thf(d4_xboole_0, axiom,
% 1.87/2.05    (![A:$i,B:$i,C:$i]:
% 1.87/2.05     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.87/2.05       ( ![D:$i]:
% 1.87/2.05         ( ( r2_hidden @ D @ C ) <=>
% 1.87/2.05           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.87/2.05  thf('2', plain,
% 1.87/2.05      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X10 @ X9)
% 1.87/2.05          | (r2_hidden @ X10 @ X8)
% 1.87/2.05          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 1.87/2.05      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.87/2.05  thf('3', plain,
% 1.87/2.05      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.87/2.05         ((r2_hidden @ X10 @ X8)
% 1.87/2.05          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.87/2.05      inference('simplify', [status(thm)], ['2'])).
% 1.87/2.05  thf('4', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0))),
% 1.87/2.05      inference('sup-', [status(thm)], ['1', '3'])).
% 1.87/2.05  thf(t69_enumset1, axiom,
% 1.87/2.05    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.87/2.05  thf('5', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 1.87/2.05      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.87/2.05  thf(t70_enumset1, axiom,
% 1.87/2.05    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.87/2.05  thf('6', plain,
% 1.87/2.05      (![X41 : $i, X42 : $i]:
% 1.87/2.05         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 1.87/2.05      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.87/2.05  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.87/2.05  thf(zf_stmt_2, axiom,
% 1.87/2.05    (![A:$i,B:$i,C:$i,D:$i]:
% 1.87/2.05     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.87/2.05       ( ![E:$i]:
% 1.87/2.05         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.87/2.05  thf('7', plain,
% 1.87/2.05      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X38 @ X37)
% 1.87/2.05          | ~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 1.87/2.05          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 1.87/2.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.87/2.05  thf('8', plain,
% 1.87/2.05      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 1.87/2.05         (~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 1.87/2.05          | ~ (r2_hidden @ X38 @ (k1_enumset1 @ X36 @ X35 @ X34)))),
% 1.87/2.05      inference('simplify', [status(thm)], ['7'])).
% 1.87/2.05  thf('9', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.87/2.05          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.87/2.05      inference('sup-', [status(thm)], ['6', '8'])).
% 1.87/2.05  thf('10', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.87/2.05          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.87/2.05      inference('sup-', [status(thm)], ['5', '9'])).
% 1.87/2.05  thf('11', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.87/2.05          | ~ (zip_tseitin_0 @ (sk_C_1 @ (k1_tarski @ X0) @ X1) @ X0 @ X0 @ X0))),
% 1.87/2.05      inference('sup-', [status(thm)], ['4', '10'])).
% 1.87/2.05  thf('12', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         (((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0))
% 1.87/2.05          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0))
% 1.87/2.05          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0))
% 1.87/2.05          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['0', '11'])).
% 1.87/2.05  thf('13', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.87/2.05          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.87/2.05      inference('simplify', [status(thm)], ['12'])).
% 1.87/2.05  thf('14', plain,
% 1.87/2.05      (![X16 : $i, X17 : $i]:
% 1.87/2.05         ((r1_xboole_0 @ X16 @ X17)
% 1.87/2.05          | (r2_hidden @ (sk_C_1 @ X17 @ X16) @ (k3_xboole_0 @ X16 @ X17)))),
% 1.87/2.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.87/2.05  thf('15', plain,
% 1.87/2.05      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X10 @ X9)
% 1.87/2.05          | (r2_hidden @ X10 @ X7)
% 1.87/2.05          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 1.87/2.05      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.87/2.05  thf('16', plain,
% 1.87/2.05      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.87/2.05         ((r2_hidden @ X10 @ X7)
% 1.87/2.05          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.87/2.05      inference('simplify', [status(thm)], ['15'])).
% 1.87/2.05  thf('17', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1))),
% 1.87/2.05      inference('sup-', [status(thm)], ['14', '16'])).
% 1.87/2.05  thf('18', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r2_hidden @ X0 @ X1)
% 1.87/2.05          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.87/2.05          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.87/2.05      inference('sup+', [status(thm)], ['13', '17'])).
% 1.87/2.05  thf('19', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 1.87/2.05      inference('simplify', [status(thm)], ['18'])).
% 1.87/2.05  thf('20', plain,
% 1.87/2.05      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.87/2.05         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 1.87/2.05          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 1.87/2.05          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.87/2.05      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.87/2.05  thf(t2_boole, axiom,
% 1.87/2.05    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.87/2.05  thf('21', plain,
% 1.87/2.05      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 1.87/2.05      inference('cnf', [status(esa)], [t2_boole])).
% 1.87/2.05  thf('22', plain,
% 1.87/2.05      (![X16 : $i, X18 : $i, X19 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 1.87/2.05          | ~ (r1_xboole_0 @ X16 @ X19))),
% 1.87/2.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.87/2.05  thf('23', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.87/2.05      inference('sup-', [status(thm)], ['21', '22'])).
% 1.87/2.05  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.87/2.05  thf('24', plain, (![X27 : $i]: (r1_xboole_0 @ X27 @ k1_xboole_0)),
% 1.87/2.05      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.87/2.05  thf('25', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.87/2.05      inference('demod', [status(thm)], ['23', '24'])).
% 1.87/2.05  thf('26', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 1.87/2.05          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['20', '25'])).
% 1.87/2.05  thf('27', plain,
% 1.87/2.05      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 1.87/2.05      inference('cnf', [status(esa)], [t2_boole])).
% 1.87/2.05  thf('28', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 1.87/2.05          | ((X1) = (k1_xboole_0)))),
% 1.87/2.05      inference('demod', [status(thm)], ['26', '27'])).
% 1.87/2.05  thf(commutativity_k3_xboole_0, axiom,
% 1.87/2.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.87/2.05  thf('29', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.87/2.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.87/2.05  thf('30', plain,
% 1.87/2.05      (![X16 : $i, X18 : $i, X19 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 1.87/2.05          | ~ (r1_xboole_0 @ X16 @ X19))),
% 1.87/2.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.87/2.05  thf('31', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.87/2.05          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.87/2.05      inference('sup-', [status(thm)], ['29', '30'])).
% 1.87/2.05  thf('32', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.87/2.05      inference('sup-', [status(thm)], ['28', '31'])).
% 1.87/2.05  thf('33', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r2_hidden @ X0 @ X1)
% 1.87/2.05          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['19', '32'])).
% 1.87/2.05  thf(t100_xboole_1, axiom,
% 1.87/2.05    (![A:$i,B:$i]:
% 1.87/2.05     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.87/2.05  thf('34', plain,
% 1.87/2.05      (![X20 : $i, X21 : $i]:
% 1.87/2.05         ((k4_xboole_0 @ X20 @ X21)
% 1.87/2.05           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 1.87/2.05      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.87/2.05  thf('35', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 1.87/2.05            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 1.87/2.05          | (r2_hidden @ X1 @ X0))),
% 1.87/2.05      inference('sup+', [status(thm)], ['33', '34'])).
% 1.87/2.05  thf('36', plain,
% 1.87/2.05      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 1.87/2.05      inference('cnf', [status(esa)], [t2_boole])).
% 1.87/2.05  thf('37', plain,
% 1.87/2.05      (![X20 : $i, X21 : $i]:
% 1.87/2.05         ((k4_xboole_0 @ X20 @ X21)
% 1.87/2.05           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 1.87/2.05      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.87/2.05  thf('38', plain,
% 1.87/2.05      (![X0 : $i]:
% 1.87/2.05         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.87/2.05      inference('sup+', [status(thm)], ['36', '37'])).
% 1.87/2.05  thf('39', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 1.87/2.05            = (k4_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 1.87/2.05          | (r2_hidden @ X1 @ X0))),
% 1.87/2.05      inference('demod', [status(thm)], ['35', '38'])).
% 1.87/2.05  thf(t68_zfmisc_1, conjecture,
% 1.87/2.05    (![A:$i,B:$i]:
% 1.87/2.05     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.87/2.05       ( r2_hidden @ A @ B ) ))).
% 1.87/2.05  thf(zf_stmt_3, negated_conjecture,
% 1.87/2.05    (~( ![A:$i,B:$i]:
% 1.87/2.05        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.87/2.05          ( r2_hidden @ A @ B ) ) )),
% 1.87/2.05    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 1.87/2.05  thf('40', plain,
% 1.87/2.05      (((r2_hidden @ sk_A @ sk_B)
% 1.87/2.05        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.87/2.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.87/2.05  thf('41', plain,
% 1.87/2.05      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 1.87/2.05         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.87/2.05      inference('split', [status(esa)], ['40'])).
% 1.87/2.05  thf('42', plain,
% 1.87/2.05      ((~ (r2_hidden @ sk_A @ sk_B)
% 1.87/2.05        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 1.87/2.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.87/2.05  thf('43', plain,
% 1.87/2.05      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.87/2.05       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.87/2.05      inference('split', [status(esa)], ['42'])).
% 1.87/2.05  thf('44', plain,
% 1.87/2.05      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.87/2.05         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 1.87/2.05          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 1.87/2.05          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.87/2.05      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.87/2.05  thf('45', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.87/2.05      inference('demod', [status(thm)], ['23', '24'])).
% 1.87/2.05  thf('46', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.87/2.05          | ((X1) = (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['44', '45'])).
% 1.87/2.05  thf('47', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.87/2.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.87/2.05  thf('48', plain,
% 1.87/2.05      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 1.87/2.05      inference('cnf', [status(esa)], [t2_boole])).
% 1.87/2.05  thf('49', plain,
% 1.87/2.05      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.87/2.05      inference('sup+', [status(thm)], ['47', '48'])).
% 1.87/2.05  thf('50', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.87/2.05          | ((X1) = (k1_xboole_0)))),
% 1.87/2.05      inference('demod', [status(thm)], ['46', '49'])).
% 1.87/2.05  thf('51', plain,
% 1.87/2.05      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.87/2.05      inference('split', [status(esa)], ['40'])).
% 1.87/2.05  thf(l1_zfmisc_1, axiom,
% 1.87/2.05    (![A:$i,B:$i]:
% 1.87/2.05     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.87/2.05  thf('52', plain,
% 1.87/2.05      (![X61 : $i, X63 : $i]:
% 1.87/2.05         ((r1_tarski @ (k1_tarski @ X61) @ X63) | ~ (r2_hidden @ X61 @ X63))),
% 1.87/2.05      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.87/2.05  thf('53', plain,
% 1.87/2.05      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 1.87/2.05         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['51', '52'])).
% 1.87/2.05  thf(t1_boole, axiom,
% 1.87/2.05    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.87/2.05  thf('54', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.87/2.05      inference('cnf', [status(esa)], [t1_boole])).
% 1.87/2.05  thf(t43_xboole_1, axiom,
% 1.87/2.05    (![A:$i,B:$i,C:$i]:
% 1.87/2.05     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.87/2.05       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.87/2.05  thf('55', plain,
% 1.87/2.05      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.87/2.05         ((r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X26)
% 1.87/2.05          | ~ (r1_tarski @ X24 @ (k2_xboole_0 @ X25 @ X26)))),
% 1.87/2.05      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.87/2.05  thf('56', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         (~ (r1_tarski @ X1 @ X0)
% 1.87/2.05          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 1.87/2.05      inference('sup-', [status(thm)], ['54', '55'])).
% 1.87/2.05  thf('57', plain,
% 1.87/2.05      (((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ k1_xboole_0))
% 1.87/2.05         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['53', '56'])).
% 1.87/2.05  thf(d3_tarski, axiom,
% 1.87/2.05    (![A:$i,B:$i]:
% 1.87/2.05     ( ( r1_tarski @ A @ B ) <=>
% 1.87/2.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.87/2.05  thf('58', plain,
% 1.87/2.05      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.87/2.05         (~ (r2_hidden @ X2 @ X3)
% 1.87/2.05          | (r2_hidden @ X2 @ X4)
% 1.87/2.05          | ~ (r1_tarski @ X3 @ X4))),
% 1.87/2.05      inference('cnf', [status(esa)], [d3_tarski])).
% 1.87/2.05  thf('59', plain,
% 1.87/2.05      ((![X0 : $i]:
% 1.87/2.05          ((r2_hidden @ X0 @ k1_xboole_0)
% 1.87/2.05           | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 1.87/2.05         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['57', '58'])).
% 1.87/2.05  thf('60', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.87/2.05      inference('demod', [status(thm)], ['23', '24'])).
% 1.87/2.05  thf('61', plain,
% 1.87/2.05      ((![X0 : $i]:
% 1.87/2.05          ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 1.87/2.05         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.87/2.05      inference('clc', [status(thm)], ['59', '60'])).
% 1.87/2.05  thf('62', plain,
% 1.87/2.05      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 1.87/2.05         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['50', '61'])).
% 1.87/2.05  thf('63', plain,
% 1.87/2.05      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 1.87/2.05         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.87/2.05      inference('split', [status(esa)], ['42'])).
% 1.87/2.05  thf('64', plain,
% 1.87/2.05      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.87/2.05         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 1.87/2.05             ((r2_hidden @ sk_A @ sk_B)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['62', '63'])).
% 1.87/2.05  thf('65', plain,
% 1.87/2.05      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 1.87/2.05       ~ ((r2_hidden @ sk_A @ sk_B))),
% 1.87/2.05      inference('simplify', [status(thm)], ['64'])).
% 1.87/2.05  thf('66', plain,
% 1.87/2.05      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 1.87/2.05       ((r2_hidden @ sk_A @ sk_B))),
% 1.87/2.05      inference('split', [status(esa)], ['40'])).
% 1.87/2.05  thf('67', plain,
% 1.87/2.05      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.87/2.05      inference('sat_resolution*', [status(thm)], ['43', '65', '66'])).
% 1.87/2.05  thf('68', plain,
% 1.87/2.05      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.87/2.05      inference('simpl_trail', [status(thm)], ['41', '67'])).
% 1.87/2.05  thf('69', plain,
% 1.87/2.05      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))
% 1.87/2.05        | (r2_hidden @ sk_A @ sk_B))),
% 1.87/2.05      inference('sup+', [status(thm)], ['39', '68'])).
% 1.87/2.05  thf('70', plain,
% 1.87/2.05      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.87/2.05      inference('split', [status(esa)], ['42'])).
% 1.87/2.05  thf('71', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 1.87/2.05      inference('sat_resolution*', [status(thm)], ['43', '65'])).
% 1.87/2.05  thf('72', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.87/2.05      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 1.87/2.05  thf('73', plain,
% 1.87/2.05      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 1.87/2.05      inference('clc', [status(thm)], ['69', '72'])).
% 1.87/2.05  thf('74', plain,
% 1.87/2.05      (![X0 : $i]:
% 1.87/2.05         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.87/2.05      inference('sup+', [status(thm)], ['36', '37'])).
% 1.87/2.05  thf('75', plain,
% 1.87/2.05      (![X3 : $i, X5 : $i]:
% 1.87/2.05         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.87/2.05      inference('cnf', [status(esa)], [d3_tarski])).
% 1.87/2.05  thf('76', plain,
% 1.87/2.05      (![X3 : $i, X5 : $i]:
% 1.87/2.05         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.87/2.05      inference('cnf', [status(esa)], [d3_tarski])).
% 1.87/2.05  thf('77', plain,
% 1.87/2.05      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.87/2.05      inference('sup-', [status(thm)], ['75', '76'])).
% 1.87/2.05  thf('78', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.87/2.05      inference('simplify', [status(thm)], ['77'])).
% 1.87/2.05  thf('79', plain,
% 1.87/2.05      (![X61 : $i, X62 : $i]:
% 1.87/2.05         ((r2_hidden @ X61 @ X62) | ~ (r1_tarski @ (k1_tarski @ X61) @ X62))),
% 1.87/2.05      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.87/2.05  thf('80', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.87/2.05      inference('sup-', [status(thm)], ['78', '79'])).
% 1.87/2.05  thf(t1_xboole_0, axiom,
% 1.87/2.05    (![A:$i,B:$i,C:$i]:
% 1.87/2.05     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.87/2.05       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.87/2.05  thf('81', plain,
% 1.87/2.05      (![X12 : $i, X13 : $i, X15 : $i]:
% 1.87/2.05         ((r2_hidden @ X12 @ (k5_xboole_0 @ X13 @ X15))
% 1.87/2.05          | (r2_hidden @ X12 @ X15)
% 1.87/2.05          | ~ (r2_hidden @ X12 @ X13))),
% 1.87/2.05      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.87/2.05  thf('82', plain,
% 1.87/2.05      (![X0 : $i, X1 : $i]:
% 1.87/2.05         ((r2_hidden @ X0 @ X1)
% 1.87/2.05          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.87/2.05      inference('sup-', [status(thm)], ['80', '81'])).
% 1.87/2.05  thf('83', plain,
% 1.87/2.05      (![X0 : $i]:
% 1.87/2.05         ((r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 1.87/2.05          | (r2_hidden @ X0 @ k1_xboole_0))),
% 1.87/2.05      inference('sup+', [status(thm)], ['74', '82'])).
% 1.87/2.05  thf('84', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.87/2.05      inference('demod', [status(thm)], ['23', '24'])).
% 1.87/2.05  thf('85', plain,
% 1.87/2.05      (![X0 : $i]:
% 1.87/2.05         (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 1.87/2.06      inference('clc', [status(thm)], ['83', '84'])).
% 1.87/2.06  thf('86', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.87/2.06      inference('sup-', [status(thm)], ['78', '79'])).
% 1.87/2.06  thf('87', plain,
% 1.87/2.06      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.87/2.06         (~ (r2_hidden @ X6 @ X7)
% 1.87/2.06          | ~ (r2_hidden @ X6 @ X8)
% 1.87/2.06          | (r2_hidden @ X6 @ X9)
% 1.87/2.06          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 1.87/2.06      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.87/2.06  thf('88', plain,
% 1.87/2.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.87/2.06         ((r2_hidden @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 1.87/2.06          | ~ (r2_hidden @ X6 @ X8)
% 1.87/2.06          | ~ (r2_hidden @ X6 @ X7))),
% 1.87/2.06      inference('simplify', [status(thm)], ['87'])).
% 1.87/2.06  thf('89', plain,
% 1.87/2.06      (![X0 : $i, X1 : $i]:
% 1.87/2.06         (~ (r2_hidden @ X0 @ X1)
% 1.87/2.06          | (r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.87/2.06      inference('sup-', [status(thm)], ['86', '88'])).
% 1.87/2.06  thf('90', plain,
% 1.87/2.06      (![X0 : $i]:
% 1.87/2.06         (r2_hidden @ X0 @ 
% 1.87/2.06          (k3_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) @ 
% 1.87/2.06           (k1_tarski @ X0)))),
% 1.87/2.06      inference('sup-', [status(thm)], ['85', '89'])).
% 1.87/2.06  thf('91', plain,
% 1.87/2.06      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.87/2.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.87/2.06  thf('92', plain,
% 1.87/2.06      (![X0 : $i]:
% 1.87/2.06         (r2_hidden @ X0 @ 
% 1.87/2.06          (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 1.87/2.06           (k4_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 1.87/2.06      inference('demod', [status(thm)], ['90', '91'])).
% 1.87/2.06  thf('93', plain,
% 1.87/2.06      (![X16 : $i, X18 : $i, X19 : $i]:
% 1.87/2.06         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 1.87/2.06          | ~ (r1_xboole_0 @ X16 @ X19))),
% 1.87/2.06      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.87/2.06  thf('94', plain,
% 1.87/2.06      (![X0 : $i]:
% 1.87/2.06         ~ (r1_xboole_0 @ (k1_tarski @ X0) @ 
% 1.87/2.06            (k4_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 1.87/2.06      inference('sup-', [status(thm)], ['92', '93'])).
% 1.87/2.06  thf('95', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 1.87/2.06      inference('sup-', [status(thm)], ['73', '94'])).
% 1.87/2.06  thf('96', plain, (![X27 : $i]: (r1_xboole_0 @ X27 @ k1_xboole_0)),
% 1.87/2.06      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.87/2.06  thf('97', plain, ($false), inference('demod', [status(thm)], ['95', '96'])).
% 1.87/2.06  
% 1.87/2.06  % SZS output end Refutation
% 1.87/2.06  
% 1.90/2.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
