%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C2zX5k0nsL

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:55 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 615 expanded)
%              Number of leaves         :   32 ( 205 expanded)
%              Depth                    :   22
%              Number of atoms          : 1227 (4706 expanded)
%              Number of equality atoms :  119 ( 486 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( X25 = X26 )
      | ( X25 = X27 )
      | ( X25 = X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
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

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X30 @ X31 @ X32 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X30 @ X31 @ X32 )
      | ~ ( r2_hidden @ X34 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
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
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('24',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('60',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X46 ) @ X47 )
      | ( r2_hidden @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('61',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('62',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('67',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('80',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['77','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['76','89'])).

thf('91',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('93',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['90','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','104'])).

thf('106',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('111',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('112',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(demod,[status(thm)],['105','106','114'])).

thf('116',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('123',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('126',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','115','116','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C2zX5k0nsL
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.76/1.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.76/1.95  % Solved by: fo/fo7.sh
% 1.76/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.76/1.95  % done 3040 iterations in 1.503s
% 1.76/1.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.76/1.95  % SZS output start Refutation
% 1.76/1.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.76/1.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.76/1.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.76/1.95  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.76/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.76/1.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.76/1.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.76/1.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.76/1.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.76/1.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.76/1.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.76/1.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.76/1.95  thf(sk_B_type, type, sk_B: $i > $i).
% 1.76/1.95  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.76/1.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.76/1.95  thf(t65_zfmisc_1, conjecture,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.76/1.95       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.76/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.76/1.95    (~( ![A:$i,B:$i]:
% 1.76/1.95        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.76/1.95          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.76/1.95    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.76/1.95  thf('0', plain,
% 1.76/1.95      (((r2_hidden @ sk_B_1 @ sk_A)
% 1.76/1.95        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('1', plain,
% 1.76/1.95      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 1.76/1.95       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.76/1.95      inference('split', [status(esa)], ['0'])).
% 1.76/1.95  thf('2', plain,
% 1.76/1.95      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 1.76/1.95      inference('split', [status(esa)], ['0'])).
% 1.76/1.95  thf(d1_enumset1, axiom,
% 1.76/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.95     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.76/1.95       ( ![E:$i]:
% 1.76/1.95         ( ( r2_hidden @ E @ D ) <=>
% 1.76/1.95           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.76/1.95  thf(zf_stmt_1, axiom,
% 1.76/1.95    (![E:$i,C:$i,B:$i,A:$i]:
% 1.76/1.95     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.76/1.95       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.76/1.95  thf('3', plain,
% 1.76/1.95      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.76/1.95         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 1.76/1.95          | ((X25) = (X26))
% 1.76/1.95          | ((X25) = (X27))
% 1.76/1.95          | ((X25) = (X28)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.76/1.95  thf(t7_xboole_0, axiom,
% 1.76/1.95    (![A:$i]:
% 1.76/1.95     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.76/1.95          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.76/1.95  thf('4', plain,
% 1.76/1.95      (![X12 : $i]:
% 1.76/1.95         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 1.76/1.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.76/1.95  thf(t69_enumset1, axiom,
% 1.76/1.95    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.76/1.95  thf('5', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.76/1.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.76/1.95  thf(t70_enumset1, axiom,
% 1.76/1.95    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.76/1.95  thf('6', plain,
% 1.76/1.95      (![X37 : $i, X38 : $i]:
% 1.76/1.95         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 1.76/1.95      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.76/1.95  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.76/1.95  thf(zf_stmt_3, axiom,
% 1.76/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.95     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.76/1.95       ( ![E:$i]:
% 1.76/1.95         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.76/1.95  thf('7', plain,
% 1.76/1.95      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X34 @ X33)
% 1.76/1.95          | ~ (zip_tseitin_0 @ X34 @ X30 @ X31 @ X32)
% 1.76/1.95          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.76/1.95  thf('8', plain,
% 1.76/1.95      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 1.76/1.95         (~ (zip_tseitin_0 @ X34 @ X30 @ X31 @ X32)
% 1.76/1.95          | ~ (r2_hidden @ X34 @ (k1_enumset1 @ X32 @ X31 @ X30)))),
% 1.76/1.95      inference('simplify', [status(thm)], ['7'])).
% 1.76/1.95  thf('9', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.76/1.95          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['6', '8'])).
% 1.76/1.95  thf('10', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.76/1.95          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['5', '9'])).
% 1.76/1.95  thf('11', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.76/1.95          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['4', '10'])).
% 1.76/1.95  thf('12', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 1.76/1.95          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 1.76/1.95          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 1.76/1.95          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['3', '11'])).
% 1.76/1.95  thf('13', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.76/1.95          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 1.76/1.95      inference('simplify', [status(thm)], ['12'])).
% 1.76/1.95  thf('14', plain,
% 1.76/1.95      (![X12 : $i]:
% 1.76/1.95         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 1.76/1.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.76/1.95  thf('15', plain,
% 1.76/1.95      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 1.76/1.95        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.95  thf('16', plain,
% 1.76/1.95      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 1.76/1.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.76/1.95      inference('split', [status(esa)], ['15'])).
% 1.76/1.95  thf(d5_xboole_0, axiom,
% 1.76/1.95    (![A:$i,B:$i,C:$i]:
% 1.76/1.95     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.76/1.95       ( ![D:$i]:
% 1.76/1.95         ( ( r2_hidden @ D @ C ) <=>
% 1.76/1.95           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.76/1.95  thf('17', plain,
% 1.76/1.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X6 @ X5)
% 1.76/1.95          | ~ (r2_hidden @ X6 @ X4)
% 1.76/1.95          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.76/1.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.76/1.95  thf('18', plain,
% 1.76/1.95      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X6 @ X4)
% 1.76/1.95          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.76/1.95      inference('simplify', [status(thm)], ['17'])).
% 1.76/1.95  thf('19', plain,
% 1.76/1.95      ((![X0 : $i]:
% 1.76/1.95          (~ (r2_hidden @ X0 @ sk_A)
% 1.76/1.95           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1))))
% 1.76/1.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.76/1.95      inference('sup-', [status(thm)], ['16', '18'])).
% 1.76/1.95  thf('20', plain,
% 1.76/1.95      (((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 1.76/1.95         | ~ (r2_hidden @ (sk_B @ (k1_tarski @ sk_B_1)) @ sk_A)))
% 1.76/1.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.76/1.95      inference('sup-', [status(thm)], ['14', '19'])).
% 1.76/1.95  thf('21', plain,
% 1.76/1.95      (((~ (r2_hidden @ sk_B_1 @ sk_A)
% 1.76/1.95         | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 1.76/1.95         | ((k1_tarski @ sk_B_1) = (k1_xboole_0))))
% 1.76/1.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.76/1.95      inference('sup-', [status(thm)], ['13', '20'])).
% 1.76/1.95  thf('22', plain,
% 1.76/1.95      (((((k1_tarski @ sk_B_1) = (k1_xboole_0)) | ~ (r2_hidden @ sk_B_1 @ sk_A)))
% 1.76/1.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.76/1.95      inference('simplify', [status(thm)], ['21'])).
% 1.76/1.95  thf('23', plain,
% 1.76/1.95      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 1.76/1.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 1.76/1.95             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['2', '22'])).
% 1.76/1.95  thf('24', plain,
% 1.76/1.95      (![X37 : $i, X38 : $i]:
% 1.76/1.95         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 1.76/1.95      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.76/1.95  thf('25', plain,
% 1.76/1.95      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.76/1.95         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 1.76/1.95          | (r2_hidden @ X29 @ X33)
% 1.76/1.95          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.76/1.95  thf('26', plain,
% 1.76/1.95      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.76/1.95         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 1.76/1.95          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 1.76/1.95      inference('simplify', [status(thm)], ['25'])).
% 1.76/1.95  thf('27', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.76/1.95          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.76/1.95      inference('sup+', [status(thm)], ['24', '26'])).
% 1.76/1.95  thf('28', plain,
% 1.76/1.95      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.76/1.95         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 1.76/1.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.76/1.95  thf('29', plain,
% 1.76/1.95      (![X24 : $i, X26 : $i, X27 : $i]:
% 1.76/1.95         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 1.76/1.95      inference('simplify', [status(thm)], ['28'])).
% 1.76/1.95  thf('30', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['27', '29'])).
% 1.76/1.95  thf('31', plain,
% 1.76/1.95      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.76/1.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.76/1.95  thf(t36_xboole_1, axiom,
% 1.76/1.95    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.76/1.95  thf('32', plain,
% 1.76/1.95      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 1.76/1.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.76/1.95  thf(l32_xboole_1, axiom,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.76/1.95  thf('33', plain,
% 1.76/1.95      (![X13 : $i, X15 : $i]:
% 1.76/1.95         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 1.76/1.95          | ~ (r1_tarski @ X13 @ X15))),
% 1.76/1.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.76/1.95  thf('34', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['32', '33'])).
% 1.76/1.95  thf('35', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['32', '33'])).
% 1.76/1.95  thf('36', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['34', '35'])).
% 1.76/1.95  thf(t48_xboole_1, axiom,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.76/1.95  thf('37', plain,
% 1.76/1.95      (![X22 : $i, X23 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.76/1.95           = (k3_xboole_0 @ X22 @ X23))),
% 1.76/1.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.76/1.95  thf('38', plain,
% 1.76/1.95      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['36', '37'])).
% 1.76/1.95  thf(commutativity_k3_xboole_0, axiom,
% 1.76/1.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.76/1.95  thf('39', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.95  thf('40', plain,
% 1.76/1.95      (![X22 : $i, X23 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.76/1.95           = (k3_xboole_0 @ X22 @ X23))),
% 1.76/1.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.76/1.95  thf('41', plain,
% 1.76/1.95      (![X13 : $i, X14 : $i]:
% 1.76/1.95         ((r1_tarski @ X13 @ X14)
% 1.76/1.95          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 1.76/1.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.76/1.95  thf('42', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 1.76/1.95          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['40', '41'])).
% 1.76/1.95  thf('43', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 1.76/1.95          | (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['39', '42'])).
% 1.76/1.95  thf('44', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.76/1.95          | (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['38', '43'])).
% 1.76/1.95  thf('45', plain,
% 1.76/1.95      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.76/1.95      inference('simplify', [status(thm)], ['44'])).
% 1.76/1.95  thf('46', plain,
% 1.76/1.95      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['36', '37'])).
% 1.76/1.95  thf('47', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.95  thf(t100_xboole_1, axiom,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.76/1.95  thf('48', plain,
% 1.76/1.95      (![X16 : $i, X17 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X16 @ X17)
% 1.76/1.95           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.76/1.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.76/1.95  thf('49', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X0 @ X1)
% 1.76/1.95           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.76/1.95      inference('sup+', [status(thm)], ['47', '48'])).
% 1.76/1.95  thf('50', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['46', '49'])).
% 1.76/1.95  thf('51', plain,
% 1.76/1.95      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.76/1.95      inference('demod', [status(thm)], ['45', '50'])).
% 1.76/1.95  thf(t28_xboole_1, axiom,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.76/1.95  thf('52', plain,
% 1.76/1.95      (![X18 : $i, X19 : $i]:
% 1.76/1.95         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.76/1.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/1.95  thf('53', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['51', '52'])).
% 1.76/1.95  thf('54', plain,
% 1.76/1.95      (![X22 : $i, X23 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.76/1.95           = (k3_xboole_0 @ X22 @ X23))),
% 1.76/1.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.76/1.95  thf('55', plain,
% 1.76/1.95      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 1.76/1.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.76/1.95  thf('56', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.76/1.95      inference('sup+', [status(thm)], ['54', '55'])).
% 1.76/1.95  thf('57', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.76/1.95      inference('sup+', [status(thm)], ['53', '56'])).
% 1.76/1.95  thf('58', plain,
% 1.76/1.95      (![X18 : $i, X19 : $i]:
% 1.76/1.95         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.76/1.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/1.95  thf('59', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['57', '58'])).
% 1.76/1.95  thf(l27_zfmisc_1, axiom,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.76/1.95  thf('60', plain,
% 1.76/1.95      (![X46 : $i, X47 : $i]:
% 1.76/1.95         ((r1_xboole_0 @ (k1_tarski @ X46) @ X47) | (r2_hidden @ X46 @ X47))),
% 1.76/1.95      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.76/1.95  thf('61', plain,
% 1.76/1.95      (![X12 : $i]:
% 1.76/1.95         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 1.76/1.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.76/1.95  thf(t4_xboole_0, axiom,
% 1.76/1.95    (![A:$i,B:$i]:
% 1.76/1.95     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.76/1.95            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.76/1.95       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.76/1.95            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.76/1.95  thf('62', plain,
% 1.76/1.95      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.76/1.95          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.76/1.95      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.76/1.95  thf('63', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['61', '62'])).
% 1.76/1.95  thf('64', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((r2_hidden @ X1 @ X0)
% 1.76/1.95          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['60', '63'])).
% 1.76/1.95  thf('65', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.95  thf('66', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.76/1.95      inference('sup+', [status(thm)], ['54', '55'])).
% 1.76/1.95  thf('67', plain,
% 1.76/1.95      (![X18 : $i, X19 : $i]:
% 1.76/1.95         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.76/1.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/1.95  thf('68', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.76/1.95           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['66', '67'])).
% 1.76/1.95  thf('69', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.95  thf('70', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.76/1.95           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('demod', [status(thm)], ['68', '69'])).
% 1.76/1.95  thf('71', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.76/1.95           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('sup+', [status(thm)], ['65', '70'])).
% 1.76/1.95  thf('72', plain,
% 1.76/1.95      (![X22 : $i, X23 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.76/1.95           = (k3_xboole_0 @ X22 @ X23))),
% 1.76/1.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.76/1.95  thf('73', plain,
% 1.76/1.95      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X6 @ X4)
% 1.76/1.95          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.76/1.95      inference('simplify', [status(thm)], ['17'])).
% 1.76/1.95  thf('74', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.76/1.95          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['72', '73'])).
% 1.76/1.95  thf('75', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.76/1.95          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))))),
% 1.76/1.95      inference('sup-', [status(thm)], ['71', '74'])).
% 1.76/1.95  thf('76', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 1.76/1.95          | (r2_hidden @ X1 @ X0)
% 1.76/1.95          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 1.76/1.95      inference('sup-', [status(thm)], ['64', '75'])).
% 1.76/1.95  thf('77', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['46', '49'])).
% 1.76/1.95  thf('78', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['51', '52'])).
% 1.76/1.95  thf('79', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.76/1.95      inference('sup+', [status(thm)], ['54', '55'])).
% 1.76/1.95  thf('80', plain,
% 1.76/1.95      (![X13 : $i, X15 : $i]:
% 1.76/1.95         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 1.76/1.95          | ~ (r1_tarski @ X13 @ X15))),
% 1.76/1.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.76/1.95  thf('81', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['79', '80'])).
% 1.76/1.95  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['78', '81'])).
% 1.76/1.95  thf('83', plain,
% 1.76/1.95      (![X22 : $i, X23 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.76/1.95           = (k3_xboole_0 @ X22 @ X23))),
% 1.76/1.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.76/1.95  thf('84', plain,
% 1.76/1.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['82', '83'])).
% 1.76/1.95  thf('85', plain,
% 1.76/1.95      (![X0 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['46', '49'])).
% 1.76/1.95  thf('86', plain,
% 1.76/1.95      (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.76/1.95      inference('demod', [status(thm)], ['84', '85'])).
% 1.76/1.95  thf('87', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['57', '58'])).
% 1.76/1.95  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['86', '87'])).
% 1.76/1.95  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.76/1.95      inference('demod', [status(thm)], ['77', '88'])).
% 1.76/1.95  thf('90', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ X0)
% 1.76/1.95          | (r2_hidden @ X1 @ X0)
% 1.76/1.95          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 1.76/1.95      inference('demod', [status(thm)], ['76', '89'])).
% 1.76/1.95  thf('91', plain,
% 1.76/1.95      (![X22 : $i, X23 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.76/1.95           = (k3_xboole_0 @ X22 @ X23))),
% 1.76/1.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.76/1.95  thf('92', plain,
% 1.76/1.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X6 @ X5)
% 1.76/1.95          | (r2_hidden @ X6 @ X3)
% 1.76/1.95          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.76/1.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.76/1.95  thf('93', plain,
% 1.76/1.95      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.76/1.95         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.76/1.95      inference('simplify', [status(thm)], ['92'])).
% 1.76/1.95  thf('94', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['91', '93'])).
% 1.76/1.95  thf('95', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.76/1.95          | (r2_hidden @ X1 @ X0))),
% 1.76/1.95      inference('clc', [status(thm)], ['90', '94'])).
% 1.76/1.95  thf('96', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.76/1.95          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['59', '95'])).
% 1.76/1.95  thf('97', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 1.76/1.95          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['31', '96'])).
% 1.76/1.95  thf('98', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['30', '97'])).
% 1.76/1.95  thf('99', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['57', '58'])).
% 1.76/1.95  thf('100', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.95  thf('101', plain,
% 1.76/1.95      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.76/1.95          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.76/1.95      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.76/1.95  thf('102', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.76/1.95          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['100', '101'])).
% 1.76/1.95  thf('103', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['99', '102'])).
% 1.76/1.95  thf('104', plain,
% 1.76/1.95      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['98', '103'])).
% 1.76/1.95  thf('105', plain,
% 1.76/1.95      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 1.76/1.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 1.76/1.95             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['23', '104'])).
% 1.76/1.95  thf('106', plain,
% 1.76/1.95      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 1.76/1.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 1.76/1.95             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['2', '22'])).
% 1.76/1.95  thf('107', plain,
% 1.76/1.95      (![X8 : $i, X9 : $i]:
% 1.76/1.95         ((r1_xboole_0 @ X8 @ X9)
% 1.76/1.95          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.76/1.95      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.76/1.95  thf('108', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['91', '93'])).
% 1.76/1.95  thf('109', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 1.76/1.95      inference('sup-', [status(thm)], ['107', '108'])).
% 1.76/1.95  thf('110', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['32', '33'])).
% 1.76/1.95  thf('111', plain,
% 1.76/1.95      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X6 @ X4)
% 1.76/1.95          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.76/1.95      inference('simplify', [status(thm)], ['17'])).
% 1.76/1.95  thf('112', plain,
% 1.76/1.95      (![X0 : $i, X2 : $i]:
% 1.76/1.95         (~ (r2_hidden @ X2 @ k1_xboole_0) | ~ (r2_hidden @ X2 @ X0))),
% 1.76/1.95      inference('sup-', [status(thm)], ['110', '111'])).
% 1.76/1.95  thf('113', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.76/1.95      inference('condensation', [status(thm)], ['112'])).
% 1.76/1.95  thf('114', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.76/1.95      inference('sup-', [status(thm)], ['109', '113'])).
% 1.76/1.95  thf('115', plain,
% 1.76/1.95      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 1.76/1.95       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.76/1.95      inference('demod', [status(thm)], ['105', '106', '114'])).
% 1.76/1.95  thf('116', plain,
% 1.76/1.95      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 1.76/1.95       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.76/1.95      inference('split', [status(esa)], ['15'])).
% 1.76/1.95  thf('117', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((r2_hidden @ X1 @ X0)
% 1.76/1.95          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['60', '63'])).
% 1.76/1.95  thf('118', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         ((k4_xboole_0 @ X0 @ X1)
% 1.76/1.95           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.76/1.95      inference('sup+', [status(thm)], ['47', '48'])).
% 1.76/1.95  thf('119', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 1.76/1.95            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 1.76/1.95          | (r2_hidden @ X1 @ X0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['117', '118'])).
% 1.76/1.95  thf('120', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.76/1.95      inference('sup+', [status(thm)], ['86', '87'])).
% 1.76/1.95  thf('121', plain,
% 1.76/1.95      (![X0 : $i, X1 : $i]:
% 1.76/1.95         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 1.76/1.95          | (r2_hidden @ X1 @ X0))),
% 1.76/1.95      inference('demod', [status(thm)], ['119', '120'])).
% 1.76/1.95  thf('122', plain,
% 1.76/1.95      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 1.76/1.95         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.76/1.95      inference('split', [status(esa)], ['0'])).
% 1.76/1.95  thf('123', plain,
% 1.76/1.95      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A)))
% 1.76/1.95         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.76/1.95      inference('sup-', [status(thm)], ['121', '122'])).
% 1.76/1.95  thf('124', plain,
% 1.76/1.95      (((r2_hidden @ sk_B_1 @ sk_A))
% 1.76/1.95         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.76/1.95      inference('simplify', [status(thm)], ['123'])).
% 1.76/1.95  thf('125', plain,
% 1.76/1.95      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 1.76/1.95      inference('split', [status(esa)], ['15'])).
% 1.76/1.95  thf('126', plain,
% 1.76/1.95      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 1.76/1.95       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.76/1.95      inference('sup-', [status(thm)], ['124', '125'])).
% 1.76/1.95  thf('127', plain, ($false),
% 1.76/1.95      inference('sat_resolution*', [status(thm)], ['1', '115', '116', '126'])).
% 1.76/1.95  
% 1.76/1.95  % SZS output end Refutation
% 1.76/1.95  
% 1.76/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
