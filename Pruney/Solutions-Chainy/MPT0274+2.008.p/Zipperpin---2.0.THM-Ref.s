%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IL3TFsXhUb

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:33 EST 2020

% Result     : Theorem 18.63s
% Output     : Refutation 18.63s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 774 expanded)
%              Number of leaves         :   35 ( 255 expanded)
%              Depth                    :   21
%              Number of atoms          : 1056 (6977 expanded)
%              Number of equality atoms :   85 ( 651 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
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

thf('4',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 )
      | ( r2_hidden @ X48 @ X52 )
      | ( X52
       != ( k1_enumset1 @ X51 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ X48 @ ( k1_enumset1 @ X51 @ X50 @ X49 ) )
      | ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X44 != X43 )
      | ~ ( zip_tseitin_0 @ X44 @ X45 @ X46 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X43: $i,X45: $i,X46: $i] :
      ~ ( zip_tseitin_0 @ X43 @ X45 @ X46 @ X43 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_xboole_0 @ X39 @ X40 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X39 @ X40 ) @ ( k2_xboole_0 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X35 @ X36 ) @ X37 )
      = ( k5_xboole_0 @ X35 @ ( k5_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_xboole_0 @ X39 @ X40 )
      = ( k5_xboole_0 @ X39 @ ( k5_xboole_0 @ X40 @ ( k2_xboole_0 @ X39 @ X40 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X38: $i] :
      ( ( k5_xboole_0 @ X38 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X35 @ X36 ) @ X37 )
      = ( k5_xboole_0 @ X35 @ ( k5_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k2_tarski @ X42 @ X41 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X82: $i,X83: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X82 @ X83 ) )
      = ( k2_xboole_0 @ X82 @ X83 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X82: $i,X83: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X82 @ X83 ) )
      = ( k2_xboole_0 @ X82 @ X83 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_xboole_0 @ X39 @ X40 )
      = ( k5_xboole_0 @ X39 @ ( k5_xboole_0 @ X40 @ ( k2_xboole_0 @ X39 @ X40 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X38: $i] :
      ( ( k5_xboole_0 @ X38 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['40'])).

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

thf('42',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','45'])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('49',plain,(
    ! [X84: $i,X85: $i,X86: $i] :
      ( ( r2_hidden @ X84 @ X85 )
      | ( r1_xboole_0 @ ( k2_tarski @ X84 @ X86 ) @ X85 )
      | ( r2_hidden @ X86 @ X85 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('50',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X33 @ X34 ) @ X34 )
        = X33 )
      | ~ ( r1_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('55',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X33 @ X34 ) @ X34 )
        = X33 )
      | ~ ( r1_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','64'])).

thf('66',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ X33 @ X34 )
        = X33 )
      | ~ ( r1_xboole_0 @ X33 @ X34 ) ) ),
    inference(demod,[status(thm)],['50','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['40'])).

thf('69',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['40'])).

thf('70',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('72',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ X33 @ X34 )
        = X33 )
      | ~ ( r1_xboole_0 @ X33 @ X34 ) ) ),
    inference(demod,[status(thm)],['50','65'])).

thf('74',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_C_2 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k2_tarski @ X42 @ X41 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('78',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','82'])).

thf('84',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['40'])).

thf('85',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','46','83','84'])).

thf('86',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['68','85'])).

thf('87',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C_2 )
    | ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['67','86'])).

thf('88',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['89'])).

thf('92',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','46','83','84','91'])).

thf('93',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['90','92'])).

thf('94',plain,(
    r2_hidden @ sk_A @ sk_C_2 ),
    inference(clc,[status(thm)],['88','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['48','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IL3TFsXhUb
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.63/18.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.63/18.83  % Solved by: fo/fo7.sh
% 18.63/18.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.63/18.83  % done 13198 iterations in 18.370s
% 18.63/18.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.63/18.83  % SZS output start Refutation
% 18.63/18.83  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 18.63/18.83  thf(sk_C_2_type, type, sk_C_2: $i).
% 18.63/18.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 18.63/18.83  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 18.63/18.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 18.63/18.83  thf(sk_B_type, type, sk_B: $i).
% 18.63/18.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 18.63/18.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 18.63/18.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 18.63/18.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.63/18.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 18.63/18.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 18.63/18.83  thf(sk_A_type, type, sk_A: $i).
% 18.63/18.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 18.63/18.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 18.63/18.83  thf(t72_zfmisc_1, conjecture,
% 18.63/18.83    (![A:$i,B:$i,C:$i]:
% 18.63/18.83     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 18.63/18.83       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 18.63/18.83  thf(zf_stmt_0, negated_conjecture,
% 18.63/18.83    (~( ![A:$i,B:$i,C:$i]:
% 18.63/18.83        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 18.63/18.83          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 18.63/18.83    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 18.63/18.83  thf('0', plain,
% 18.63/18.83      ((~ (r2_hidden @ sk_A @ sk_C_2)
% 18.63/18.83        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83            = (k2_tarski @ sk_A @ sk_B)))),
% 18.63/18.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.63/18.83  thf('1', plain,
% 18.63/18.83      ((~ (r2_hidden @ sk_A @ sk_C_2)) <= (~ ((r2_hidden @ sk_A @ sk_C_2)))),
% 18.63/18.83      inference('split', [status(esa)], ['0'])).
% 18.63/18.83  thf('2', plain,
% 18.63/18.83      (~ ((r2_hidden @ sk_A @ sk_C_2)) | 
% 18.63/18.83       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          = (k2_tarski @ sk_A @ sk_B)))),
% 18.63/18.83      inference('split', [status(esa)], ['0'])).
% 18.63/18.83  thf(t70_enumset1, axiom,
% 18.63/18.83    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 18.63/18.83  thf('3', plain,
% 18.63/18.83      (![X55 : $i, X56 : $i]:
% 18.63/18.83         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 18.63/18.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 18.63/18.83  thf(d1_enumset1, axiom,
% 18.63/18.83    (![A:$i,B:$i,C:$i,D:$i]:
% 18.63/18.83     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 18.63/18.83       ( ![E:$i]:
% 18.63/18.83         ( ( r2_hidden @ E @ D ) <=>
% 18.63/18.83           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 18.63/18.83  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 18.63/18.83  thf(zf_stmt_2, axiom,
% 18.63/18.83    (![E:$i,C:$i,B:$i,A:$i]:
% 18.63/18.83     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 18.63/18.83       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 18.63/18.83  thf(zf_stmt_3, axiom,
% 18.63/18.83    (![A:$i,B:$i,C:$i,D:$i]:
% 18.63/18.83     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 18.63/18.83       ( ![E:$i]:
% 18.63/18.83         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 18.63/18.83  thf('4', plain,
% 18.63/18.83      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 18.63/18.83         ((zip_tseitin_0 @ X48 @ X49 @ X50 @ X51)
% 18.63/18.83          | (r2_hidden @ X48 @ X52)
% 18.63/18.83          | ((X52) != (k1_enumset1 @ X51 @ X50 @ X49)))),
% 18.63/18.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.63/18.83  thf('5', plain,
% 18.63/18.83      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 18.63/18.83         ((r2_hidden @ X48 @ (k1_enumset1 @ X51 @ X50 @ X49))
% 18.63/18.83          | (zip_tseitin_0 @ X48 @ X49 @ X50 @ X51))),
% 18.63/18.83      inference('simplify', [status(thm)], ['4'])).
% 18.63/18.83  thf('6', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.63/18.83         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 18.63/18.83          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 18.63/18.83      inference('sup+', [status(thm)], ['3', '5'])).
% 18.63/18.83  thf('7', plain,
% 18.63/18.83      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 18.63/18.83         (((X44) != (X43)) | ~ (zip_tseitin_0 @ X44 @ X45 @ X46 @ X43))),
% 18.63/18.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.63/18.83  thf('8', plain,
% 18.63/18.83      (![X43 : $i, X45 : $i, X46 : $i]:
% 18.63/18.83         ~ (zip_tseitin_0 @ X43 @ X45 @ X46 @ X43)),
% 18.63/18.83      inference('simplify', [status(thm)], ['7'])).
% 18.63/18.83  thf('9', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 18.63/18.83      inference('sup-', [status(thm)], ['6', '8'])).
% 18.63/18.83  thf('10', plain,
% 18.63/18.83      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          = (k2_tarski @ sk_A @ sk_B)))
% 18.63/18.83         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83                = (k2_tarski @ sk_A @ sk_B))))),
% 18.63/18.83      inference('split', [status(esa)], ['0'])).
% 18.63/18.83  thf(t95_xboole_1, axiom,
% 18.63/18.83    (![A:$i,B:$i]:
% 18.63/18.83     ( ( k3_xboole_0 @ A @ B ) =
% 18.63/18.83       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 18.63/18.83  thf('11', plain,
% 18.63/18.83      (![X39 : $i, X40 : $i]:
% 18.63/18.83         ((k3_xboole_0 @ X39 @ X40)
% 18.63/18.83           = (k5_xboole_0 @ (k5_xboole_0 @ X39 @ X40) @ 
% 18.63/18.83              (k2_xboole_0 @ X39 @ X40)))),
% 18.63/18.83      inference('cnf', [status(esa)], [t95_xboole_1])).
% 18.63/18.83  thf(t91_xboole_1, axiom,
% 18.63/18.83    (![A:$i,B:$i,C:$i]:
% 18.63/18.83     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 18.63/18.83       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 18.63/18.83  thf('12', plain,
% 18.63/18.83      (![X35 : $i, X36 : $i, X37 : $i]:
% 18.63/18.83         ((k5_xboole_0 @ (k5_xboole_0 @ X35 @ X36) @ X37)
% 18.63/18.83           = (k5_xboole_0 @ X35 @ (k5_xboole_0 @ X36 @ X37)))),
% 18.63/18.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 18.63/18.83  thf('13', plain,
% 18.63/18.83      (![X39 : $i, X40 : $i]:
% 18.63/18.83         ((k3_xboole_0 @ X39 @ X40)
% 18.63/18.83           = (k5_xboole_0 @ X39 @ 
% 18.63/18.83              (k5_xboole_0 @ X40 @ (k2_xboole_0 @ X39 @ X40))))),
% 18.63/18.83      inference('demod', [status(thm)], ['11', '12'])).
% 18.63/18.83  thf(t92_xboole_1, axiom,
% 18.63/18.83    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 18.63/18.83  thf('14', plain, (![X38 : $i]: ((k5_xboole_0 @ X38 @ X38) = (k1_xboole_0))),
% 18.63/18.83      inference('cnf', [status(esa)], [t92_xboole_1])).
% 18.63/18.83  thf('15', plain,
% 18.63/18.83      (![X35 : $i, X36 : $i, X37 : $i]:
% 18.63/18.83         ((k5_xboole_0 @ (k5_xboole_0 @ X35 @ X36) @ X37)
% 18.63/18.83           = (k5_xboole_0 @ X35 @ (k5_xboole_0 @ X36 @ X37)))),
% 18.63/18.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 18.63/18.83  thf('16', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 18.63/18.83           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.63/18.83      inference('sup+', [status(thm)], ['14', '15'])).
% 18.63/18.83  thf(commutativity_k5_xboole_0, axiom,
% 18.63/18.83    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 18.63/18.83  thf('17', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 18.63/18.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 18.63/18.83  thf(t5_boole, axiom,
% 18.63/18.83    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 18.63/18.83  thf('18', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 18.63/18.83      inference('cnf', [status(esa)], [t5_boole])).
% 18.63/18.83  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 18.63/18.83      inference('sup+', [status(thm)], ['17', '18'])).
% 18.63/18.83  thf('20', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.63/18.83      inference('demod', [status(thm)], ['16', '19'])).
% 18.63/18.83  thf('21', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 18.63/18.83           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 18.63/18.83      inference('sup+', [status(thm)], ['13', '20'])).
% 18.63/18.83  thf(t100_xboole_1, axiom,
% 18.63/18.83    (![A:$i,B:$i]:
% 18.63/18.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 18.63/18.83  thf('22', plain,
% 18.63/18.83      (![X18 : $i, X19 : $i]:
% 18.63/18.83         ((k4_xboole_0 @ X18 @ X19)
% 18.63/18.83           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 18.63/18.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.63/18.83  thf('23', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 18.63/18.83           = (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('demod', [status(thm)], ['21', '22'])).
% 18.63/18.83  thf(l97_xboole_1, axiom,
% 18.63/18.83    (![A:$i,B:$i]:
% 18.63/18.83     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 18.63/18.83  thf('24', plain,
% 18.63/18.83      (![X16 : $i, X17 : $i]:
% 18.63/18.83         (r1_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k5_xboole_0 @ X16 @ X17))),
% 18.63/18.83      inference('cnf', [status(esa)], [l97_xboole_1])).
% 18.63/18.83  thf('25', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 18.63/18.83          (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('sup+', [status(thm)], ['23', '24'])).
% 18.63/18.83  thf(commutativity_k2_tarski, axiom,
% 18.63/18.83    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 18.63/18.83  thf('26', plain,
% 18.63/18.83      (![X41 : $i, X42 : $i]:
% 18.63/18.83         ((k2_tarski @ X42 @ X41) = (k2_tarski @ X41 @ X42))),
% 18.63/18.83      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 18.63/18.83  thf(l51_zfmisc_1, axiom,
% 18.63/18.83    (![A:$i,B:$i]:
% 18.63/18.83     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 18.63/18.83  thf('27', plain,
% 18.63/18.83      (![X82 : $i, X83 : $i]:
% 18.63/18.83         ((k3_tarski @ (k2_tarski @ X82 @ X83)) = (k2_xboole_0 @ X82 @ X83))),
% 18.63/18.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 18.63/18.83  thf('28', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 18.63/18.83      inference('sup+', [status(thm)], ['26', '27'])).
% 18.63/18.83  thf('29', plain,
% 18.63/18.83      (![X82 : $i, X83 : $i]:
% 18.63/18.83         ((k3_tarski @ (k2_tarski @ X82 @ X83)) = (k2_xboole_0 @ X82 @ X83))),
% 18.63/18.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 18.63/18.83  thf('30', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.63/18.83      inference('sup+', [status(thm)], ['28', '29'])).
% 18.63/18.83  thf(t6_xboole_1, axiom,
% 18.63/18.83    (![A:$i,B:$i]:
% 18.63/18.83     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 18.63/18.83  thf('31', plain,
% 18.63/18.83      (![X29 : $i, X30 : $i]:
% 18.63/18.83         ((k2_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30))
% 18.63/18.83           = (k2_xboole_0 @ X29 @ X30))),
% 18.63/18.83      inference('cnf', [status(esa)], [t6_xboole_1])).
% 18.63/18.83  thf('32', plain,
% 18.63/18.83      (![X39 : $i, X40 : $i]:
% 18.63/18.83         ((k3_xboole_0 @ X39 @ X40)
% 18.63/18.83           = (k5_xboole_0 @ X39 @ 
% 18.63/18.83              (k5_xboole_0 @ X40 @ (k2_xboole_0 @ X39 @ X40))))),
% 18.63/18.83      inference('demod', [status(thm)], ['11', '12'])).
% 18.63/18.83  thf('33', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 18.63/18.83           = (k5_xboole_0 @ X1 @ 
% 18.63/18.83              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 18.63/18.83      inference('sup+', [status(thm)], ['31', '32'])).
% 18.63/18.83  thf('34', plain, (![X38 : $i]: ((k5_xboole_0 @ X38 @ X38) = (k1_xboole_0))),
% 18.63/18.83      inference('cnf', [status(esa)], [t92_xboole_1])).
% 18.63/18.83  thf('35', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 18.63/18.83           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 18.63/18.83      inference('demod', [status(thm)], ['33', '34'])).
% 18.63/18.83  thf('36', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 18.63/18.83      inference('cnf', [status(esa)], [t5_boole])).
% 18.63/18.83  thf('37', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 18.63/18.83      inference('demod', [status(thm)], ['35', '36'])).
% 18.63/18.83  thf('38', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 18.63/18.83      inference('sup+', [status(thm)], ['30', '37'])).
% 18.63/18.83  thf('39', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('demod', [status(thm)], ['25', '38'])).
% 18.63/18.83  thf('40', plain,
% 18.63/18.83      (((r2_hidden @ sk_B @ sk_C_2)
% 18.63/18.83        | (r2_hidden @ sk_A @ sk_C_2)
% 18.63/18.83        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83            != (k2_tarski @ sk_A @ sk_B)))),
% 18.63/18.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.63/18.83  thf('41', plain,
% 18.63/18.83      (((r2_hidden @ sk_A @ sk_C_2)) <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 18.63/18.83      inference('split', [status(esa)], ['40'])).
% 18.63/18.83  thf(t3_xboole_0, axiom,
% 18.63/18.83    (![A:$i,B:$i]:
% 18.63/18.83     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 18.63/18.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 18.63/18.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 18.63/18.83            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 18.63/18.83  thf('42', plain,
% 18.63/18.83      (![X12 : $i, X14 : $i, X15 : $i]:
% 18.63/18.83         (~ (r2_hidden @ X14 @ X12)
% 18.63/18.83          | ~ (r2_hidden @ X14 @ X15)
% 18.63/18.83          | ~ (r1_xboole_0 @ X12 @ X15))),
% 18.63/18.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 18.63/18.83  thf('43', plain,
% 18.63/18.83      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 18.63/18.83         <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 18.63/18.83      inference('sup-', [status(thm)], ['41', '42'])).
% 18.63/18.83  thf('44', plain,
% 18.63/18.83      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_2)))
% 18.63/18.83         <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 18.63/18.83      inference('sup-', [status(thm)], ['39', '43'])).
% 18.63/18.83  thf('45', plain,
% 18.63/18.83      ((~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B)))
% 18.63/18.83         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83                = (k2_tarski @ sk_A @ sk_B))) & 
% 18.63/18.83             ((r2_hidden @ sk_A @ sk_C_2)))),
% 18.63/18.83      inference('sup-', [status(thm)], ['10', '44'])).
% 18.63/18.83  thf('46', plain,
% 18.63/18.83      (~ ((r2_hidden @ sk_A @ sk_C_2)) | 
% 18.63/18.83       ~
% 18.63/18.83       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          = (k2_tarski @ sk_A @ sk_B)))),
% 18.63/18.83      inference('sup-', [status(thm)], ['9', '45'])).
% 18.63/18.83  thf('47', plain, (~ ((r2_hidden @ sk_A @ sk_C_2))),
% 18.63/18.83      inference('sat_resolution*', [status(thm)], ['2', '46'])).
% 18.63/18.83  thf('48', plain, (~ (r2_hidden @ sk_A @ sk_C_2)),
% 18.63/18.83      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 18.63/18.83  thf(t57_zfmisc_1, axiom,
% 18.63/18.83    (![A:$i,B:$i,C:$i]:
% 18.63/18.83     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 18.63/18.83          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 18.63/18.83  thf('49', plain,
% 18.63/18.83      (![X84 : $i, X85 : $i, X86 : $i]:
% 18.63/18.83         ((r2_hidden @ X84 @ X85)
% 18.63/18.83          | (r1_xboole_0 @ (k2_tarski @ X84 @ X86) @ X85)
% 18.63/18.83          | (r2_hidden @ X86 @ X85))),
% 18.63/18.83      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 18.63/18.83  thf(t88_xboole_1, axiom,
% 18.63/18.83    (![A:$i,B:$i]:
% 18.63/18.83     ( ( r1_xboole_0 @ A @ B ) =>
% 18.63/18.83       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 18.63/18.83  thf('50', plain,
% 18.63/18.83      (![X33 : $i, X34 : $i]:
% 18.63/18.83         (((k4_xboole_0 @ (k2_xboole_0 @ X33 @ X34) @ X34) = (X33))
% 18.63/18.83          | ~ (r1_xboole_0 @ X33 @ X34))),
% 18.63/18.83      inference('cnf', [status(esa)], [t88_xboole_1])).
% 18.63/18.83  thf('51', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.63/18.83      inference('sup+', [status(thm)], ['28', '29'])).
% 18.63/18.83  thf('52', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('demod', [status(thm)], ['25', '38'])).
% 18.63/18.83  thf('53', plain,
% 18.63/18.83      (![X12 : $i, X13 : $i]:
% 18.63/18.83         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12))),
% 18.63/18.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 18.63/18.83  thf('54', plain,
% 18.63/18.83      (![X12 : $i, X13 : $i]:
% 18.63/18.83         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X13))),
% 18.63/18.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 18.63/18.83  thf('55', plain,
% 18.63/18.83      (![X12 : $i, X14 : $i, X15 : $i]:
% 18.63/18.83         (~ (r2_hidden @ X14 @ X12)
% 18.63/18.83          | ~ (r2_hidden @ X14 @ X15)
% 18.63/18.83          | ~ (r1_xboole_0 @ X12 @ X15))),
% 18.63/18.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 18.63/18.83  thf('56', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.63/18.83         ((r1_xboole_0 @ X1 @ X0)
% 18.63/18.83          | ~ (r1_xboole_0 @ X0 @ X2)
% 18.63/18.83          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 18.63/18.83      inference('sup-', [status(thm)], ['54', '55'])).
% 18.63/18.83  thf('57', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((r1_xboole_0 @ X0 @ X1)
% 18.63/18.83          | ~ (r1_xboole_0 @ X1 @ X0)
% 18.63/18.83          | (r1_xboole_0 @ X0 @ X1))),
% 18.63/18.83      inference('sup-', [status(thm)], ['53', '56'])).
% 18.63/18.83  thf('58', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 18.63/18.83      inference('simplify', [status(thm)], ['57'])).
% 18.63/18.83  thf('59', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 18.63/18.83      inference('sup-', [status(thm)], ['52', '58'])).
% 18.63/18.83  thf('60', plain,
% 18.63/18.83      (![X33 : $i, X34 : $i]:
% 18.63/18.83         (((k4_xboole_0 @ (k2_xboole_0 @ X33 @ X34) @ X34) = (X33))
% 18.63/18.83          | ~ (r1_xboole_0 @ X33 @ X34))),
% 18.63/18.83      inference('cnf', [status(esa)], [t88_xboole_1])).
% 18.63/18.83  thf('61', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 18.63/18.83           = (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('sup-', [status(thm)], ['59', '60'])).
% 18.63/18.83  thf('62', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.63/18.83      inference('sup+', [status(thm)], ['28', '29'])).
% 18.63/18.83  thf(t39_xboole_1, axiom,
% 18.63/18.83    (![A:$i,B:$i]:
% 18.63/18.83     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 18.63/18.83  thf('63', plain,
% 18.63/18.83      (![X23 : $i, X24 : $i]:
% 18.63/18.83         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 18.63/18.83           = (k2_xboole_0 @ X23 @ X24))),
% 18.63/18.83      inference('cnf', [status(esa)], [t39_xboole_1])).
% 18.63/18.83  thf('64', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 18.63/18.83           = (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('demod', [status(thm)], ['61', '62', '63'])).
% 18.63/18.83  thf('65', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]:
% 18.63/18.83         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 18.63/18.83           = (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('sup+', [status(thm)], ['51', '64'])).
% 18.63/18.83  thf('66', plain,
% 18.63/18.83      (![X33 : $i, X34 : $i]:
% 18.63/18.83         (((k4_xboole_0 @ X33 @ X34) = (X33)) | ~ (r1_xboole_0 @ X33 @ X34))),
% 18.63/18.83      inference('demod', [status(thm)], ['50', '65'])).
% 18.63/18.83  thf('67', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.63/18.83         ((r2_hidden @ X1 @ X0)
% 18.63/18.83          | (r2_hidden @ X2 @ X0)
% 18.63/18.83          | ((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1)))),
% 18.63/18.83      inference('sup-', [status(thm)], ['49', '66'])).
% 18.63/18.83  thf('68', plain,
% 18.63/18.83      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          != (k2_tarski @ sk_A @ sk_B)))
% 18.63/18.83         <= (~
% 18.63/18.83             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83                = (k2_tarski @ sk_A @ sk_B))))),
% 18.63/18.83      inference('split', [status(esa)], ['40'])).
% 18.63/18.83  thf('69', plain,
% 18.63/18.83      (((r2_hidden @ sk_B @ sk_C_2)) <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 18.63/18.83      inference('split', [status(esa)], ['40'])).
% 18.63/18.83  thf('70', plain,
% 18.63/18.83      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          = (k2_tarski @ sk_A @ sk_B)))
% 18.63/18.83         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83                = (k2_tarski @ sk_A @ sk_B))))),
% 18.63/18.83      inference('split', [status(esa)], ['0'])).
% 18.63/18.83  thf('71', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('demod', [status(thm)], ['25', '38'])).
% 18.63/18.83  thf('72', plain,
% 18.63/18.83      (((r1_xboole_0 @ sk_C_2 @ (k2_tarski @ sk_A @ sk_B)))
% 18.63/18.83         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83                = (k2_tarski @ sk_A @ sk_B))))),
% 18.63/18.83      inference('sup+', [status(thm)], ['70', '71'])).
% 18.63/18.83  thf('73', plain,
% 18.63/18.83      (![X33 : $i, X34 : $i]:
% 18.63/18.83         (((k4_xboole_0 @ X33 @ X34) = (X33)) | ~ (r1_xboole_0 @ X33 @ X34))),
% 18.63/18.83      inference('demod', [status(thm)], ['50', '65'])).
% 18.63/18.83  thf('74', plain,
% 18.63/18.83      ((((k4_xboole_0 @ sk_C_2 @ (k2_tarski @ sk_A @ sk_B)) = (sk_C_2)))
% 18.63/18.83         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83                = (k2_tarski @ sk_A @ sk_B))))),
% 18.63/18.83      inference('sup-', [status(thm)], ['72', '73'])).
% 18.63/18.83  thf('75', plain,
% 18.63/18.83      (![X41 : $i, X42 : $i]:
% 18.63/18.83         ((k2_tarski @ X42 @ X41) = (k2_tarski @ X41 @ X42))),
% 18.63/18.83      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 18.63/18.83  thf('76', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 18.63/18.83      inference('demod', [status(thm)], ['25', '38'])).
% 18.63/18.83  thf('77', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 18.63/18.83      inference('sup-', [status(thm)], ['6', '8'])).
% 18.63/18.83  thf('78', plain,
% 18.63/18.83      (![X12 : $i, X14 : $i, X15 : $i]:
% 18.63/18.83         (~ (r2_hidden @ X14 @ X12)
% 18.63/18.83          | ~ (r2_hidden @ X14 @ X15)
% 18.63/18.83          | ~ (r1_xboole_0 @ X12 @ X15))),
% 18.63/18.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 18.63/18.83  thf('79', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.63/18.83         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 18.63/18.83          | ~ (r2_hidden @ X1 @ X2))),
% 18.63/18.83      inference('sup-', [status(thm)], ['77', '78'])).
% 18.63/18.83  thf('80', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.63/18.83         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 18.63/18.83      inference('sup-', [status(thm)], ['76', '79'])).
% 18.63/18.83  thf('81', plain,
% 18.63/18.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.63/18.83         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 18.63/18.83      inference('sup-', [status(thm)], ['75', '80'])).
% 18.63/18.83  thf('82', plain,
% 18.63/18.83      ((~ (r2_hidden @ sk_B @ sk_C_2))
% 18.63/18.83         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83                = (k2_tarski @ sk_A @ sk_B))))),
% 18.63/18.83      inference('sup-', [status(thm)], ['74', '81'])).
% 18.63/18.83  thf('83', plain,
% 18.63/18.83      (~ ((r2_hidden @ sk_B @ sk_C_2)) | 
% 18.63/18.83       ~
% 18.63/18.83       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          = (k2_tarski @ sk_A @ sk_B)))),
% 18.63/18.83      inference('sup-', [status(thm)], ['69', '82'])).
% 18.63/18.83  thf('84', plain,
% 18.63/18.83      (~
% 18.63/18.83       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          = (k2_tarski @ sk_A @ sk_B))) | 
% 18.63/18.83       ((r2_hidden @ sk_B @ sk_C_2)) | ((r2_hidden @ sk_A @ sk_C_2))),
% 18.63/18.83      inference('split', [status(esa)], ['40'])).
% 18.63/18.83  thf('85', plain,
% 18.63/18.83      (~
% 18.63/18.83       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          = (k2_tarski @ sk_A @ sk_B)))),
% 18.63/18.83      inference('sat_resolution*', [status(thm)], ['2', '46', '83', '84'])).
% 18.63/18.83  thf('86', plain,
% 18.63/18.83      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83         != (k2_tarski @ sk_A @ sk_B))),
% 18.63/18.83      inference('simpl_trail', [status(thm)], ['68', '85'])).
% 18.63/18.83  thf('87', plain,
% 18.63/18.83      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 18.63/18.83        | (r2_hidden @ sk_A @ sk_C_2)
% 18.63/18.83        | (r2_hidden @ sk_B @ sk_C_2))),
% 18.63/18.83      inference('sup-', [status(thm)], ['67', '86'])).
% 18.63/18.83  thf('88', plain,
% 18.63/18.83      (((r2_hidden @ sk_B @ sk_C_2) | (r2_hidden @ sk_A @ sk_C_2))),
% 18.63/18.83      inference('simplify', [status(thm)], ['87'])).
% 18.63/18.83  thf('89', plain,
% 18.63/18.83      ((~ (r2_hidden @ sk_B @ sk_C_2)
% 18.63/18.83        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83            = (k2_tarski @ sk_A @ sk_B)))),
% 18.63/18.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.63/18.83  thf('90', plain,
% 18.63/18.83      ((~ (r2_hidden @ sk_B @ sk_C_2)) <= (~ ((r2_hidden @ sk_B @ sk_C_2)))),
% 18.63/18.83      inference('split', [status(esa)], ['89'])).
% 18.63/18.83  thf('91', plain,
% 18.63/18.83      (~ ((r2_hidden @ sk_B @ sk_C_2)) | 
% 18.63/18.83       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 18.63/18.83          = (k2_tarski @ sk_A @ sk_B)))),
% 18.63/18.83      inference('split', [status(esa)], ['89'])).
% 18.63/18.83  thf('92', plain, (~ ((r2_hidden @ sk_B @ sk_C_2))),
% 18.63/18.83      inference('sat_resolution*', [status(thm)], ['2', '46', '83', '84', '91'])).
% 18.63/18.83  thf('93', plain, (~ (r2_hidden @ sk_B @ sk_C_2)),
% 18.63/18.83      inference('simpl_trail', [status(thm)], ['90', '92'])).
% 18.63/18.83  thf('94', plain, ((r2_hidden @ sk_A @ sk_C_2)),
% 18.63/18.83      inference('clc', [status(thm)], ['88', '93'])).
% 18.63/18.83  thf('95', plain, ($false), inference('demod', [status(thm)], ['48', '94'])).
% 18.63/18.83  
% 18.63/18.83  % SZS output end Refutation
% 18.63/18.83  
% 18.63/18.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
