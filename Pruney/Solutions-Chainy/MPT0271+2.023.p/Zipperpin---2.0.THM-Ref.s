%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kGg4iRxyAW

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:23 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 786 expanded)
%              Number of leaves         :   34 ( 249 expanded)
%              Depth                    :   24
%              Number of atoms          : 1073 (6029 expanded)
%              Number of equality atoms :  121 ( 722 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X65 ) @ X64 )
        = X64 )
      | ~ ( r2_hidden @ X65 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('6',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','25'])).

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

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( X25 = X26 )
      | ( X25 = X27 )
      | ( X25 = X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('48',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('49',plain,(
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

thf('50',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X30 @ X31 @ X32 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X30 @ X31 @ X32 )
      | ~ ( r2_hidden @ X34 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('62',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','78'])).

thf('80',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('81',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('87',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','23'])).

thf('88',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['85','88'])).

thf('90',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['85','88'])).

thf('91',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('92',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('99',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('100',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','101'])).

thf('103',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('104',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','105'])).

thf('107',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['97','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('109',plain,(
    $false ),
    inference('sup-',[status(thm)],['107','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kGg4iRxyAW
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 1007 iterations in 0.714s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.17  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.99/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.99/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.99/1.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.99/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.99/1.17  thf(t68_zfmisc_1, conjecture,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.99/1.17       ( r2_hidden @ A @ B ) ))).
% 0.99/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.17    (~( ![A:$i,B:$i]:
% 0.99/1.17        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.99/1.17          ( r2_hidden @ A @ B ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.99/1.17  thf('0', plain,
% 0.99/1.17      (((r2_hidden @ sk_A @ sk_B)
% 0.99/1.17        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('1', plain,
% 0.99/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.99/1.17         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.99/1.17      inference('split', [status(esa)], ['0'])).
% 0.99/1.17  thf('2', plain,
% 0.99/1.17      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.99/1.17        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('3', plain,
% 0.99/1.17      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.99/1.17       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.99/1.17      inference('split', [status(esa)], ['2'])).
% 0.99/1.17  thf('4', plain,
% 0.99/1.17      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.99/1.17      inference('split', [status(esa)], ['0'])).
% 0.99/1.17  thf(l22_zfmisc_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( r2_hidden @ A @ B ) =>
% 0.99/1.17       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (![X64 : $i, X65 : $i]:
% 0.99/1.17         (((k2_xboole_0 @ (k1_tarski @ X65) @ X64) = (X64))
% 0.99/1.17          | ~ (r2_hidden @ X65 @ X64))),
% 0.99/1.17      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.99/1.17  thf('6', plain,
% 0.99/1.17      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 0.99/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.17  thf(t95_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k3_xboole_0 @ A @ B ) =
% 0.99/1.17       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.99/1.17  thf('7', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ X20 @ X21)
% 0.99/1.17           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.99/1.17              (k2_xboole_0 @ X20 @ X21)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.99/1.17  thf(t91_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.99/1.17       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.99/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.99/1.17           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ X20 @ X21)
% 0.99/1.17           = (k5_xboole_0 @ X20 @ 
% 0.99/1.17              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.99/1.17      inference('demod', [status(thm)], ['7', '8'])).
% 0.99/1.17  thf('10', plain,
% 0.99/1.17      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.99/1.17          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ sk_B @ sk_B))))
% 0.99/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['6', '9'])).
% 0.99/1.17  thf(t92_xboole_1, axiom,
% 0.99/1.17    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.99/1.17  thf('11', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.99/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.99/1.17  thf(commutativity_k5_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.99/1.17  thf('12', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.99/1.17  thf('13', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.99/1.17  thf(t5_boole, axiom,
% 0.99/1.17    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.17  thf('14', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.99/1.17      inference('cnf', [status(esa)], [t5_boole])).
% 0.99/1.17  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['13', '14'])).
% 0.99/1.17  thf('16', plain,
% 0.99/1.17      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.99/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['10', '11', '12', '15'])).
% 0.99/1.17  thf(t100_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      (![X11 : $i, X12 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X11 @ X12)
% 0.99/1.17           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.99/1.17  thf('18', plain,
% 0.99/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.99/1.17          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.99/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['16', '17'])).
% 0.99/1.17  thf('19', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.99/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.99/1.17  thf('20', plain,
% 0.99/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.99/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['18', '19'])).
% 0.99/1.17  thf('21', plain,
% 0.99/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.99/1.17         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.99/1.17      inference('split', [status(esa)], ['2'])).
% 0.99/1.17  thf('22', plain,
% 0.99/1.17      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.99/1.17         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.99/1.17             ((r2_hidden @ sk_A @ sk_B)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['20', '21'])).
% 0.99/1.17  thf('23', plain,
% 0.99/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.99/1.17       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.99/1.17      inference('simplify', [status(thm)], ['22'])).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.99/1.17       ((r2_hidden @ sk_A @ sk_B))),
% 0.99/1.17      inference('split', [status(esa)], ['0'])).
% 0.99/1.17  thf('25', plain,
% 0.99/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.99/1.17      inference('sat_resolution*', [status(thm)], ['3', '23', '24'])).
% 0.99/1.17  thf('26', plain,
% 0.99/1.17      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.99/1.17      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.99/1.17  thf(d1_enumset1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.17     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.99/1.17       ( ![E:$i]:
% 0.99/1.17         ( ( r2_hidden @ E @ D ) <=>
% 0.99/1.17           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_1, axiom,
% 0.99/1.17    (![E:$i,C:$i,B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.99/1.17       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.99/1.17  thf('27', plain,
% 0.99/1.17      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.99/1.17         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.99/1.17          | ((X25) = (X26))
% 0.99/1.17          | ((X25) = (X27))
% 0.99/1.17          | ((X25) = (X28)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.17  thf(d5_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.99/1.17       ( ![D:$i]:
% 0.99/1.17         ( ( r2_hidden @ D @ C ) <=>
% 0.99/1.17           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.99/1.17  thf('28', plain,
% 0.99/1.17      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.99/1.17         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.99/1.17          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.99/1.17          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.99/1.17      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.99/1.17  thf('29', plain,
% 0.99/1.17      (![X11 : $i, X12 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X11 @ X12)
% 0.99/1.17           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.99/1.17  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['13', '14'])).
% 0.99/1.17  thf('31', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['29', '30'])).
% 0.99/1.17  thf(t98_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.99/1.17  thf('32', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X22 @ X23)
% 0.99/1.17           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.99/1.17  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['13', '14'])).
% 0.99/1.17  thf('34', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['32', '33'])).
% 0.99/1.17  thf('35', plain,
% 0.99/1.17      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.99/1.17         = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['31', '34'])).
% 0.99/1.17  thf(d10_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.17  thf('36', plain,
% 0.99/1.17      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.99/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.17  thf('37', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.99/1.17      inference('simplify', [status(thm)], ['36'])).
% 0.99/1.17  thf(t12_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.99/1.17  thf('38', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.99/1.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.99/1.17  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['37', '38'])).
% 0.99/1.17  thf('40', plain,
% 0.99/1.17      (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['35', '39'])).
% 0.99/1.17  thf('41', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['29', '30'])).
% 0.99/1.17  thf('42', plain,
% 0.99/1.17      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X6 @ X5)
% 0.99/1.17          | ~ (r2_hidden @ X6 @ X4)
% 0.99/1.17          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.99/1.17      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.99/1.17  thf('43', plain,
% 0.99/1.17      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X6 @ X4)
% 0.99/1.17          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.99/1.17      inference('simplify', [status(thm)], ['42'])).
% 0.99/1.17  thf('44', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.99/1.17          | ~ (r2_hidden @ X1 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['41', '43'])).
% 0.99/1.17  thf('45', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['40', '44'])).
% 0.99/1.17  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.99/1.17      inference('simplify', [status(thm)], ['45'])).
% 0.99/1.17  thf('47', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.99/1.17          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['28', '46'])).
% 0.99/1.17  thf(t69_enumset1, axiom,
% 0.99/1.17    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.99/1.17  thf('48', plain,
% 0.99/1.17      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.99/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.99/1.17  thf(t70_enumset1, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.99/1.17  thf('49', plain,
% 0.99/1.17      (![X37 : $i, X38 : $i]:
% 0.99/1.17         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.99/1.17      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.99/1.17  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_3, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.17     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.99/1.17       ( ![E:$i]:
% 0.99/1.17         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.99/1.17  thf('50', plain,
% 0.99/1.17      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X34 @ X33)
% 0.99/1.17          | ~ (zip_tseitin_0 @ X34 @ X30 @ X31 @ X32)
% 0.99/1.17          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.17  thf('51', plain,
% 0.99/1.17      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 0.99/1.17         (~ (zip_tseitin_0 @ X34 @ X30 @ X31 @ X32)
% 0.99/1.17          | ~ (r2_hidden @ X34 @ (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.99/1.17      inference('simplify', [status(thm)], ['50'])).
% 0.99/1.17  thf('52', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.99/1.17          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.99/1.17      inference('sup-', [status(thm)], ['49', '51'])).
% 0.99/1.17  thf('53', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.99/1.17          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['48', '52'])).
% 0.99/1.17  thf('54', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.99/1.17          | ~ (zip_tseitin_0 @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 0.99/1.17               X0 @ X0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['47', '53'])).
% 0.99/1.17  thf('55', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.99/1.17          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.99/1.17          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.99/1.17          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['27', '54'])).
% 0.99/1.17  thf('56', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.99/1.17          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.99/1.17      inference('simplify', [status(thm)], ['55'])).
% 0.99/1.17  thf('57', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.99/1.17          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['28', '46'])).
% 0.99/1.17  thf('58', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.99/1.17          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.99/1.17          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['56', '57'])).
% 0.99/1.17  thf('59', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.99/1.17          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.99/1.17      inference('simplify', [status(thm)], ['58'])).
% 0.99/1.17  thf('60', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.99/1.17          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['28', '46'])).
% 0.99/1.17  thf('61', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.99/1.17      inference('simplify', [status(thm)], ['45'])).
% 0.99/1.17  thf('62', plain,
% 0.99/1.17      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['60', '61'])).
% 0.99/1.17  thf('63', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X22 @ X23)
% 0.99/1.17           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.99/1.17  thf('64', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['62', '63'])).
% 0.99/1.17  thf('65', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.99/1.17      inference('cnf', [status(esa)], [t5_boole])).
% 0.99/1.17  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['64', '65'])).
% 0.99/1.17  thf('67', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ X20 @ X21)
% 0.99/1.17           = (k5_xboole_0 @ X20 @ 
% 0.99/1.17              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.99/1.17      inference('demod', [status(thm)], ['7', '8'])).
% 0.99/1.17  thf('68', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.99/1.17           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['66', '67'])).
% 0.99/1.17  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['13', '14'])).
% 0.99/1.17  thf('70', plain,
% 0.99/1.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['68', '69'])).
% 0.99/1.17  thf('71', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.99/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.99/1.17  thf('72', plain,
% 0.99/1.17      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.99/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.99/1.17           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.99/1.17  thf('73', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.99/1.17           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['71', '72'])).
% 0.99/1.17  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['13', '14'])).
% 0.99/1.17  thf('75', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('demod', [status(thm)], ['73', '74'])).
% 0.99/1.17  thf('76', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['70', '75'])).
% 0.99/1.17  thf('77', plain,
% 0.99/1.17      (![X11 : $i, X12 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X11 @ X12)
% 0.99/1.17           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.99/1.17  thf('78', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.99/1.17  thf('79', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.99/1.17          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['59', '78'])).
% 0.99/1.17  thf('80', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X2 @ X3)
% 0.99/1.17          | (r2_hidden @ X2 @ X4)
% 0.99/1.17          | (r2_hidden @ X2 @ X5)
% 0.99/1.17          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.99/1.17      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.99/1.17  thf('81', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.99/1.17         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.99/1.17          | (r2_hidden @ X2 @ X4)
% 0.99/1.17          | ~ (r2_hidden @ X2 @ X3))),
% 0.99/1.17      inference('simplify', [status(thm)], ['80'])).
% 0.99/1.17  thf('82', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.99/1.17          | (r2_hidden @ X0 @ X1)
% 0.99/1.17          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['79', '81'])).
% 0.99/1.17  thf('83', plain,
% 0.99/1.17      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.99/1.17        | (r2_hidden @ sk_A @ sk_B)
% 0.99/1.17        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['26', '82'])).
% 0.99/1.17  thf('84', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.99/1.17      inference('simplify', [status(thm)], ['45'])).
% 0.99/1.17  thf('85', plain,
% 0.99/1.17      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B))),
% 0.99/1.17      inference('clc', [status(thm)], ['83', '84'])).
% 0.99/1.17  thf('86', plain,
% 0.99/1.17      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.99/1.17      inference('split', [status(esa)], ['2'])).
% 0.99/1.17  thf('87', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.99/1.17      inference('sat_resolution*', [status(thm)], ['3', '23'])).
% 0.99/1.17  thf('88', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.99/1.17      inference('simpl_trail', [status(thm)], ['86', '87'])).
% 0.99/1.17  thf('89', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.99/1.17      inference('clc', [status(thm)], ['85', '88'])).
% 0.99/1.17  thf('90', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.99/1.17      inference('clc', [status(thm)], ['85', '88'])).
% 0.99/1.17  thf('91', plain,
% 0.99/1.17      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.99/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.99/1.17  thf(l51_zfmisc_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.17  thf('92', plain,
% 0.99/1.17      (![X66 : $i, X67 : $i]:
% 0.99/1.17         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.99/1.17      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.99/1.17  thf('93', plain,
% 0.99/1.17      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['91', '92'])).
% 0.99/1.17  thf('94', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['37', '38'])).
% 0.99/1.17  thf('95', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['93', '94'])).
% 0.99/1.17  thf('96', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.99/1.17      inference('sup+', [status(thm)], ['90', '95'])).
% 0.99/1.17  thf('97', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['89', '96'])).
% 0.99/1.17  thf('98', plain,
% 0.99/1.17      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.99/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.99/1.17  thf('99', plain,
% 0.99/1.17      (![X37 : $i, X38 : $i]:
% 0.99/1.17         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.99/1.17      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.99/1.17  thf('100', plain,
% 0.99/1.17      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.99/1.17         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.99/1.17          | (r2_hidden @ X29 @ X33)
% 0.99/1.17          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.17  thf('101', plain,
% 0.99/1.17      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.99/1.17         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 0.99/1.17          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 0.99/1.17      inference('simplify', [status(thm)], ['100'])).
% 0.99/1.17  thf('102', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.99/1.17          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.99/1.17      inference('sup+', [status(thm)], ['99', '101'])).
% 0.99/1.17  thf('103', plain,
% 0.99/1.17      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.99/1.17         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.17  thf('104', plain,
% 0.99/1.17      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.99/1.17         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 0.99/1.17      inference('simplify', [status(thm)], ['103'])).
% 0.99/1.17  thf('105', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.99/1.17      inference('sup-', [status(thm)], ['102', '104'])).
% 0.99/1.17  thf('106', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['98', '105'])).
% 0.99/1.17  thf('107', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.99/1.17      inference('sup+', [status(thm)], ['97', '106'])).
% 0.99/1.17  thf('108', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.99/1.17      inference('simplify', [status(thm)], ['45'])).
% 0.99/1.17  thf('109', plain, ($false), inference('sup-', [status(thm)], ['107', '108'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 1.01/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
