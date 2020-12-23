%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.chti1T2zUB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:12 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 573 expanded)
%              Number of leaves         :   33 ( 183 expanded)
%              Depth                    :   21
%              Number of atoms          :  932 (5294 expanded)
%              Number of equality atoms :   85 ( 414 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X63: $i] :
      ( ( k2_tarski @ X63 @ X63 )
      = ( k1_tarski @ X63 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k1_enumset1 @ X64 @ X64 @ X65 )
      = ( k2_tarski @ X64 @ X65 ) ) ),
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

thf('15',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X34 @ X38 )
      | ( X38
       != ( k1_enumset1 @ X37 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k1_enumset1 @ X37 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X63: $i] :
      ( ( k2_tarski @ X63 @ X63 )
      = ( k1_tarski @ X63 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('18',plain,(
    ! [X95: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X95 ) )
      = X95 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('20',plain,(
    ! [X91: $i,X92: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X91 ) @ X92 )
      | ( r2_hidden @ X91 @ X92 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X93: $i,X94: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X93 @ X94 ) )
      = ( k2_xboole_0 @ X93 @ X94 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) ) @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X95: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X95 ) )
      = X95 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('40',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('42',plain,
    ( ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ sk_B )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X1 @ X2 )
        | ~ ( r1_xboole_0 @ sk_B @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','44'])).

thf('46',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ ( k2_tarski @ X1 @ X0 ) )
        | ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X1 @ X1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        | ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X0 @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','46'])).

thf('48',plain,
    ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ sk_A @ sk_A @ sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','47'])).

thf('49',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('50',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('51',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('52',plain,
    ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('54',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ~ ( zip_tseitin_0 @ X29 @ X31 @ X32 @ X29 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','55'])).

thf('57',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) ) @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,(
    ! [X93: $i,X94: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X93 @ X94 ) )
      = ( k2_xboole_0 @ X93 @ X94 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('67',plain,(
    ! [X93: $i,X94: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X93 @ X94 ) )
      = ( k2_xboole_0 @ X93 @ X94 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('68',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['58','70'])).

thf('72',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('74',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','55','73'])).

thf('75',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['57','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.chti1T2zUB
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.77/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.97  % Solved by: fo/fo7.sh
% 0.77/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.97  % done 836 iterations in 0.513s
% 0.77/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.97  % SZS output start Refutation
% 0.77/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.97  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.77/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.77/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.97  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.77/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/0.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.77/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.97  thf(t67_zfmisc_1, conjecture,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.77/0.97       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.77/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.97    (~( ![A:$i,B:$i]:
% 0.77/0.97        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.77/0.97          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.77/0.97    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.77/0.97  thf('0', plain,
% 0.77/0.97      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.77/0.97        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('1', plain,
% 0.77/0.97      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('split', [status(esa)], ['0'])).
% 0.77/0.97  thf('2', plain,
% 0.77/0.97      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.77/0.97       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.77/0.97      inference('split', [status(esa)], ['0'])).
% 0.77/0.97  thf('3', plain,
% 0.77/0.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.77/0.97      inference('split', [status(esa)], ['0'])).
% 0.77/0.97  thf(t79_xboole_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.77/0.97  thf('4', plain,
% 0.77/0.97      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.77/0.97      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.77/0.97  thf('5', plain,
% 0.77/0.97      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.77/0.97      inference('sup+', [status(thm)], ['3', '4'])).
% 0.77/0.97  thf(t3_xboole_0, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.77/0.97            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.77/0.97       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.77/0.97            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.77/0.97  thf('6', plain,
% 0.77/0.97      (![X3 : $i, X4 : $i]:
% 0.77/0.97         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.77/0.97  thf('7', plain,
% 0.77/0.97      (![X3 : $i, X4 : $i]:
% 0.77/0.97         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.77/0.97  thf('8', plain,
% 0.77/0.97      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.77/0.97         (~ (r2_hidden @ X5 @ X3)
% 0.77/0.97          | ~ (r2_hidden @ X5 @ X6)
% 0.77/0.97          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.77/0.97  thf('9', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.97         ((r1_xboole_0 @ X1 @ X0)
% 0.77/0.97          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.77/0.97          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.77/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.97  thf('10', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         ((r1_xboole_0 @ X0 @ X1)
% 0.77/0.97          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.77/0.97          | (r1_xboole_0 @ X0 @ X1))),
% 0.77/0.97      inference('sup-', [status(thm)], ['6', '9'])).
% 0.77/0.97  thf('11', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.77/0.97      inference('simplify', [status(thm)], ['10'])).
% 0.77/0.97  thf('12', plain,
% 0.77/0.97      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.77/0.97      inference('sup-', [status(thm)], ['5', '11'])).
% 0.77/0.97  thf(t69_enumset1, axiom,
% 0.77/0.97    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.77/0.97  thf('13', plain,
% 0.77/0.97      (![X63 : $i]: ((k2_tarski @ X63 @ X63) = (k1_tarski @ X63))),
% 0.77/0.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.97  thf(t70_enumset1, axiom,
% 0.77/0.97    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.77/0.97  thf('14', plain,
% 0.77/0.97      (![X64 : $i, X65 : $i]:
% 0.77/0.97         ((k1_enumset1 @ X64 @ X64 @ X65) = (k2_tarski @ X64 @ X65))),
% 0.77/0.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.77/0.97  thf(d1_enumset1, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.97     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.77/0.97       ( ![E:$i]:
% 0.77/0.97         ( ( r2_hidden @ E @ D ) <=>
% 0.77/0.97           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.77/0.97  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.77/0.97  thf(zf_stmt_2, axiom,
% 0.77/0.97    (![E:$i,C:$i,B:$i,A:$i]:
% 0.77/0.97     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.77/0.97       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.77/0.97  thf(zf_stmt_3, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.97     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.77/0.97       ( ![E:$i]:
% 0.77/0.97         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.77/0.97  thf('15', plain,
% 0.77/0.97      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.77/0.97         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 0.77/0.97          | (r2_hidden @ X34 @ X38)
% 0.77/0.97          | ((X38) != (k1_enumset1 @ X37 @ X36 @ X35)))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.97  thf('16', plain,
% 0.77/0.97      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.77/0.97         ((r2_hidden @ X34 @ (k1_enumset1 @ X37 @ X36 @ X35))
% 0.77/0.97          | (zip_tseitin_0 @ X34 @ X35 @ X36 @ X37))),
% 0.77/0.97      inference('simplify', [status(thm)], ['15'])).
% 0.77/0.97  thf('17', plain,
% 0.77/0.97      (![X63 : $i]: ((k2_tarski @ X63 @ X63) = (k1_tarski @ X63))),
% 0.77/0.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.97  thf(t31_zfmisc_1, axiom,
% 0.77/0.97    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.77/0.97  thf('18', plain, (![X95 : $i]: ((k3_tarski @ (k1_tarski @ X95)) = (X95))),
% 0.77/0.97      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.77/0.97  thf('19', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['17', '18'])).
% 0.77/0.97  thf(l27_zfmisc_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.77/0.97  thf('20', plain,
% 0.77/0.97      (![X91 : $i, X92 : $i]:
% 0.77/0.97         ((r1_xboole_0 @ (k1_tarski @ X91) @ X92) | (r2_hidden @ X91 @ X92))),
% 0.77/0.97      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.77/0.97  thf(t88_xboole_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( r1_xboole_0 @ A @ B ) =>
% 0.77/0.97       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.77/0.97  thf('21', plain,
% 0.77/0.97      (![X19 : $i, X20 : $i]:
% 0.77/0.97         (((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20) = (X19))
% 0.77/0.97          | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.77/0.97      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.77/0.97  thf(l51_zfmisc_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.97  thf('22', plain,
% 0.77/0.97      (![X93 : $i, X94 : $i]:
% 0.77/0.97         ((k3_tarski @ (k2_tarski @ X93 @ X94)) = (k2_xboole_0 @ X93 @ X94))),
% 0.77/0.97      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.97  thf('23', plain,
% 0.77/0.97      (![X19 : $i, X20 : $i]:
% 0.77/0.97         (((k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X19 @ X20)) @ X20) = (X19))
% 0.77/0.97          | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.77/0.97      inference('demod', [status(thm)], ['21', '22'])).
% 0.77/0.97  thf('24', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         ((r2_hidden @ X1 @ X0)
% 0.77/0.97          | ((k4_xboole_0 @ 
% 0.77/0.97              (k3_tarski @ (k2_tarski @ (k1_tarski @ X1) @ X0)) @ X0)
% 0.77/0.97              = (k1_tarski @ X1)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['20', '23'])).
% 0.77/0.97  thf('25', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.77/0.97            = (k1_tarski @ X0))
% 0.77/0.97          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['19', '24'])).
% 0.77/0.97  thf(idempotence_k3_xboole_0, axiom,
% 0.77/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/0.97  thf('26', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/0.97      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/0.97  thf(t100_xboole_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.77/0.97  thf('27', plain,
% 0.77/0.97      (![X7 : $i, X8 : $i]:
% 0.77/0.97         ((k4_xboole_0 @ X7 @ X8)
% 0.77/0.97           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.77/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/0.97  thf('28', plain,
% 0.77/0.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['26', '27'])).
% 0.77/0.97  thf(t92_xboole_1, axiom,
% 0.77/0.97    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.77/0.97  thf('29', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.77/0.97      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/0.97  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['28', '29'])).
% 0.77/0.97  thf('31', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.77/0.97          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.77/0.97      inference('demod', [status(thm)], ['25', '30'])).
% 0.77/0.97  thf('32', plain,
% 0.77/0.97      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.77/0.97      inference('sup-', [status(thm)], ['5', '11'])).
% 0.77/0.97  thf('33', plain,
% 0.77/0.97      (((r2_hidden @ sk_A @ sk_B)
% 0.77/0.97        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('34', plain,
% 0.77/0.97      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('split', [status(esa)], ['33'])).
% 0.77/0.97  thf('35', plain,
% 0.77/0.97      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.77/0.97         (~ (r2_hidden @ X5 @ X3)
% 0.77/0.97          | ~ (r2_hidden @ X5 @ X6)
% 0.77/0.97          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.77/0.97  thf('36', plain,
% 0.77/0.97      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 0.77/0.97         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/0.97  thf('37', plain,
% 0.77/0.97      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['32', '36'])).
% 0.77/0.97  thf('38', plain,
% 0.77/0.97      ((((k1_xboole_0) = (k1_tarski @ sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['31', '37'])).
% 0.77/0.97  thf('39', plain, (![X95 : $i]: ((k3_tarski @ (k1_tarski @ X95)) = (X95))),
% 0.77/0.97      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.77/0.97  thf('40', plain,
% 0.77/0.97      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.97  thf('41', plain,
% 0.77/0.97      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('split', [status(esa)], ['33'])).
% 0.77/0.97  thf('42', plain,
% 0.77/0.97      (((r2_hidden @ (k3_tarski @ k1_xboole_0) @ sk_B))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['40', '41'])).
% 0.77/0.97  thf('43', plain,
% 0.77/0.97      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.77/0.97         (~ (r2_hidden @ X5 @ X3)
% 0.77/0.97          | ~ (r2_hidden @ X5 @ X6)
% 0.77/0.97          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.77/0.97  thf('44', plain,
% 0.77/0.97      ((![X0 : $i]:
% 0.77/0.97          (~ (r1_xboole_0 @ sk_B @ X0)
% 0.77/0.97           | ~ (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['42', '43'])).
% 0.77/0.97  thf('45', plain,
% 0.77/0.97      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.97          ((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X1 @ X2)
% 0.77/0.97           | ~ (r1_xboole_0 @ sk_B @ (k1_enumset1 @ X2 @ X1 @ X0))))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['16', '44'])).
% 0.77/0.97  thf('46', plain,
% 0.77/0.97      ((![X0 : $i, X1 : $i]:
% 0.77/0.97          (~ (r1_xboole_0 @ sk_B @ (k2_tarski @ X1 @ X0))
% 0.77/0.97           | (zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X1 @ X1)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['14', '45'])).
% 0.77/0.97  thf('47', plain,
% 0.77/0.97      ((![X0 : $i]:
% 0.77/0.97          (~ (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.77/0.97           | (zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X0 @ X0)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['13', '46'])).
% 0.77/0.97  thf('48', plain,
% 0.77/0.97      (((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ sk_A @ sk_A @ sk_A))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '47'])).
% 0.77/0.97  thf('49', plain,
% 0.77/0.97      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.97  thf('50', plain,
% 0.77/0.97      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.97  thf('51', plain,
% 0.77/0.97      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.97  thf('52', plain,
% 0.77/0.97      (((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ 
% 0.77/0.97         (k3_tarski @ k1_xboole_0) @ (k3_tarski @ k1_xboole_0) @ 
% 0.77/0.97         (k3_tarski @ k1_xboole_0)))
% 0.77/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.77/0.97             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/0.97      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.77/0.97  thf('53', plain,
% 0.77/0.97      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.77/0.97         (((X30) != (X29)) | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.97  thf('54', plain,
% 0.77/0.97      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.77/0.97         ~ (zip_tseitin_0 @ X29 @ X31 @ X32 @ X29)),
% 0.77/0.97      inference('simplify', [status(thm)], ['53'])).
% 0.77/0.97  thf('55', plain,
% 0.77/0.97      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.77/0.97       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.77/0.97      inference('sup-', [status(thm)], ['52', '54'])).
% 0.77/0.97  thf('56', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.77/0.97      inference('sat_resolution*', [status(thm)], ['2', '55'])).
% 0.77/0.97  thf('57', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.77/0.97      inference('simpl_trail', [status(thm)], ['1', '56'])).
% 0.77/0.97  thf('58', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         ((r2_hidden @ X1 @ X0)
% 0.77/0.97          | ((k4_xboole_0 @ 
% 0.77/0.97              (k3_tarski @ (k2_tarski @ (k1_tarski @ X1) @ X0)) @ X0)
% 0.77/0.97              = (k1_tarski @ X1)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['20', '23'])).
% 0.77/0.97  thf(commutativity_k2_tarski, axiom,
% 0.77/0.97    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.77/0.97  thf('59', plain,
% 0.77/0.97      (![X27 : $i, X28 : $i]:
% 0.77/0.97         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.77/0.97      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.77/0.97  thf('60', plain,
% 0.77/0.97      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.77/0.97      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.77/0.97  thf('61', plain,
% 0.77/0.97      (![X19 : $i, X20 : $i]:
% 0.77/0.97         (((k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X19 @ X20)) @ X20) = (X19))
% 0.77/0.97          | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.77/0.97      inference('demod', [status(thm)], ['21', '22'])).
% 0.77/0.97  thf('62', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         ((k4_xboole_0 @ 
% 0.77/0.97           (k3_tarski @ (k2_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0)) @ X0)
% 0.77/0.97           = (k4_xboole_0 @ X1 @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['60', '61'])).
% 0.77/0.97  thf('63', plain,
% 0.77/0.97      (![X27 : $i, X28 : $i]:
% 0.77/0.97         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.77/0.97      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.77/0.97  thf('64', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         ((k4_xboole_0 @ 
% 0.77/0.97           (k3_tarski @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))) @ X0)
% 0.77/0.98           = (k4_xboole_0 @ X1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['62', '63'])).
% 0.77/0.98  thf(t39_xboole_1, axiom,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.98  thf('65', plain,
% 0.77/0.98      (![X10 : $i, X11 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.77/0.98           = (k2_xboole_0 @ X10 @ X11))),
% 0.77/0.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.98  thf('66', plain,
% 0.77/0.98      (![X93 : $i, X94 : $i]:
% 0.77/0.98         ((k3_tarski @ (k2_tarski @ X93 @ X94)) = (k2_xboole_0 @ X93 @ X94))),
% 0.77/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.98  thf('67', plain,
% 0.77/0.98      (![X93 : $i, X94 : $i]:
% 0.77/0.98         ((k3_tarski @ (k2_tarski @ X93 @ X94)) = (k2_xboole_0 @ X93 @ X94))),
% 0.77/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.98  thf('68', plain,
% 0.77/0.98      (![X10 : $i, X11 : $i]:
% 0.77/0.98         ((k3_tarski @ (k2_tarski @ X10 @ (k4_xboole_0 @ X11 @ X10)))
% 0.77/0.98           = (k3_tarski @ (k2_tarski @ X10 @ X11)))),
% 0.77/0.98      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.77/0.98  thf('69', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 0.77/0.98           = (k4_xboole_0 @ X1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['64', '68'])).
% 0.77/0.98  thf('70', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X0)
% 0.77/0.98           = (k4_xboole_0 @ X1 @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['59', '69'])).
% 0.77/0.98  thf('71', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((r2_hidden @ X1 @ X0)
% 0.77/0.98          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.77/0.98      inference('demod', [status(thm)], ['58', '70'])).
% 0.77/0.98  thf('72', plain,
% 0.77/0.98      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.77/0.98         <= (~
% 0.77/0.98             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.77/0.98      inference('split', [status(esa)], ['33'])).
% 0.77/0.98  thf('73', plain,
% 0.77/0.98      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.77/0.98       ((r2_hidden @ sk_A @ sk_B))),
% 0.77/0.98      inference('split', [status(esa)], ['33'])).
% 0.77/0.98  thf('74', plain,
% 0.77/0.98      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.77/0.98      inference('sat_resolution*', [status(thm)], ['2', '55', '73'])).
% 0.77/0.98  thf('75', plain,
% 0.77/0.98      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.77/0.98      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.77/0.98  thf('76', plain,
% 0.77/0.98      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.77/0.98      inference('sup-', [status(thm)], ['71', '75'])).
% 0.77/0.98  thf('77', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.77/0.98      inference('simplify', [status(thm)], ['76'])).
% 0.77/0.98  thf('78', plain, ($false), inference('demod', [status(thm)], ['57', '77'])).
% 0.77/0.98  
% 0.77/0.98  % SZS output end Refutation
% 0.77/0.98  
% 0.77/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
