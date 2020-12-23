%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6jPdiIMr7M

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:53 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 261 expanded)
%              Number of leaves         :   32 (  88 expanded)
%              Depth                    :   19
%              Number of atoms          :  922 (1913 expanded)
%              Number of equality atoms :   92 ( 202 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
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

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X30 @ X34 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) )
      | ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X25 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('22',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X43 ) @ X44 )
      | ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('49',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','81'])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','90'])).

thf('92',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('94',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','19','93'])).

thf('95',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['92','94'])).

thf('96',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['21','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6jPdiIMr7M
% 0.14/0.32  % Computer   : n005.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 12:35:48 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.32  % Running portfolio for 600 s
% 0.14/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.32  % Number of cores: 8
% 0.14/0.33  % Python version: Python 3.6.8
% 0.14/0.33  % Running in FO mode
% 0.79/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.03  % Solved by: fo/fo7.sh
% 0.79/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.03  % done 1644 iterations in 0.591s
% 0.79/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.03  % SZS output start Refutation
% 0.79/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.79/1.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.79/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.79/1.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.79/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.79/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.79/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.79/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.79/1.03  thf(t65_zfmisc_1, conjecture,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.79/1.03       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.79/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.03    (~( ![A:$i,B:$i]:
% 0.79/1.03        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.79/1.03          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.79/1.03    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.79/1.03  thf('0', plain,
% 0.79/1.03      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.79/1.03        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.03  thf('1', plain,
% 0.79/1.03      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.79/1.03      inference('split', [status(esa)], ['0'])).
% 0.79/1.03  thf('2', plain,
% 0.79/1.03      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.79/1.03       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.79/1.03      inference('split', [status(esa)], ['0'])).
% 0.79/1.03  thf('3', plain,
% 0.79/1.03      (((r2_hidden @ sk_B @ sk_A)
% 0.79/1.03        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.03  thf('4', plain,
% 0.79/1.03      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.79/1.03      inference('split', [status(esa)], ['3'])).
% 0.79/1.03  thf(t69_enumset1, axiom,
% 0.79/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.79/1.03  thf('5', plain, (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.79/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.79/1.03  thf(t70_enumset1, axiom,
% 0.79/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.79/1.03  thf('6', plain,
% 0.79/1.03      (![X38 : $i, X39 : $i]:
% 0.79/1.03         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.79/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.79/1.03  thf(d1_enumset1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.79/1.03       ( ![E:$i]:
% 0.79/1.03         ( ( r2_hidden @ E @ D ) <=>
% 0.79/1.03           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.79/1.03  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.79/1.03  thf(zf_stmt_2, axiom,
% 0.79/1.03    (![E:$i,C:$i,B:$i,A:$i]:
% 0.79/1.03     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.79/1.03       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.79/1.03  thf(zf_stmt_3, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.79/1.03       ( ![E:$i]:
% 0.79/1.03         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.79/1.03  thf('7', plain,
% 0.79/1.03      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.79/1.03         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 0.79/1.03          | (r2_hidden @ X30 @ X34)
% 0.79/1.03          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.79/1.03  thf('8', plain,
% 0.79/1.03      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.79/1.03         ((r2_hidden @ X30 @ (k1_enumset1 @ X33 @ X32 @ X31))
% 0.79/1.03          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33))),
% 0.79/1.03      inference('simplify', [status(thm)], ['7'])).
% 0.79/1.03  thf('9', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.79/1.03          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.79/1.03      inference('sup+', [status(thm)], ['6', '8'])).
% 0.79/1.03  thf('10', plain,
% 0.79/1.03      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.79/1.03         (((X26) != (X25)) | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X25))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/1.03  thf('11', plain,
% 0.79/1.03      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.79/1.03         ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X25)),
% 0.79/1.03      inference('simplify', [status(thm)], ['10'])).
% 0.79/1.03  thf('12', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['9', '11'])).
% 0.79/1.03  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['5', '12'])).
% 0.79/1.03  thf('14', plain,
% 0.79/1.03      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.79/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.79/1.03      inference('split', [status(esa)], ['0'])).
% 0.79/1.03  thf(d5_xboole_0, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.79/1.03       ( ![D:$i]:
% 0.79/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.79/1.03           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.79/1.03  thf('15', plain,
% 0.79/1.03      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X6 @ X5)
% 0.79/1.03          | ~ (r2_hidden @ X6 @ X4)
% 0.79/1.03          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.79/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.79/1.03  thf('16', plain,
% 0.79/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X6 @ X4)
% 0.79/1.03          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.79/1.03      inference('simplify', [status(thm)], ['15'])).
% 0.79/1.03  thf('17', plain,
% 0.79/1.03      ((![X0 : $i]:
% 0.79/1.03          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.79/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.79/1.03      inference('sup-', [status(thm)], ['14', '16'])).
% 0.79/1.03  thf('18', plain,
% 0.79/1.03      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.79/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.79/1.03      inference('sup-', [status(thm)], ['13', '17'])).
% 0.79/1.03  thf('19', plain,
% 0.79/1.03      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.79/1.03       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['4', '18'])).
% 0.79/1.03  thf('20', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.79/1.03      inference('sat_resolution*', [status(thm)], ['2', '19'])).
% 0.79/1.03  thf('21', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.79/1.03      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.79/1.03  thf(l27_zfmisc_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.79/1.03  thf('22', plain,
% 0.79/1.03      (![X43 : $i, X44 : $i]:
% 0.79/1.03         ((r1_xboole_0 @ (k1_tarski @ X43) @ X44) | (r2_hidden @ X43 @ X44))),
% 0.79/1.03      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.79/1.03  thf(t83_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/1.03  thf('23', plain,
% 0.79/1.03      (![X22 : $i, X23 : $i]:
% 0.79/1.03         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.79/1.03      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.79/1.03  thf('24', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((r2_hidden @ X1 @ X0)
% 0.79/1.03          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/1.03  thf('25', plain,
% 0.79/1.03      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.79/1.03         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.79/1.03          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.79/1.03          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.79/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.79/1.03  thf(t3_boole, axiom,
% 0.79/1.03    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/1.03  thf('26', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.79/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/1.03  thf('27', plain,
% 0.79/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X6 @ X4)
% 0.79/1.03          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.79/1.03      inference('simplify', [status(thm)], ['15'])).
% 0.79/1.03  thf('28', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['26', '27'])).
% 0.79/1.03  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.79/1.03      inference('condensation', [status(thm)], ['28'])).
% 0.79/1.03  thf('30', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.79/1.03          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['25', '29'])).
% 0.79/1.03  thf('31', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.79/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/1.03  thf(t48_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.79/1.03  thf('32', plain,
% 0.79/1.03      (![X17 : $i, X18 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.79/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.79/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/1.03  thf('33', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['31', '32'])).
% 0.79/1.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.79/1.03  thf('34', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.79/1.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.79/1.03  thf(t28_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/1.03  thf('35', plain,
% 0.79/1.03      (![X13 : $i, X14 : $i]:
% 0.79/1.03         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.79/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.79/1.03  thf('36', plain,
% 0.79/1.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['34', '35'])).
% 0.79/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.79/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.79/1.03  thf('37', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.79/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/1.03  thf('38', plain,
% 0.79/1.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['36', '37'])).
% 0.79/1.03  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/1.03      inference('demod', [status(thm)], ['33', '38'])).
% 0.79/1.03  thf('40', plain,
% 0.79/1.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['34', '35'])).
% 0.79/1.03  thf('41', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['39', '40'])).
% 0.79/1.03  thf(t49_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.79/1.03       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.79/1.03  thf('42', plain,
% 0.79/1.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.79/1.03           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.79/1.03      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/1.03  thf('43', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 0.79/1.03           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['41', '42'])).
% 0.79/1.03  thf('44', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['39', '40'])).
% 0.79/1.03  thf('45', plain,
% 0.79/1.03      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.79/1.03      inference('demod', [status(thm)], ['43', '44'])).
% 0.79/1.03  thf('46', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.79/1.03          | ((X1) = (k1_xboole_0)))),
% 0.79/1.03      inference('demod', [status(thm)], ['30', '45'])).
% 0.79/1.03  thf('47', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.79/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/1.03  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/1.03      inference('demod', [status(thm)], ['33', '38'])).
% 0.79/1.03  thf('49', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.79/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/1.03  thf('50', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.79/1.03      inference('sup+', [status(thm)], ['48', '49'])).
% 0.79/1.03  thf(d10_xboole_0, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/1.03  thf('51', plain,
% 0.79/1.03      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.79/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/1.03  thf('52', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.79/1.03      inference('simplify', [status(thm)], ['51'])).
% 0.79/1.03  thf('53', plain,
% 0.79/1.03      (![X13 : $i, X14 : $i]:
% 0.79/1.03         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.79/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.79/1.03  thf('54', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['52', '53'])).
% 0.79/1.03  thf(t100_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.79/1.03  thf('55', plain,
% 0.79/1.03      (![X11 : $i, X12 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X11 @ X12)
% 0.79/1.03           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/1.03  thf('56', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['54', '55'])).
% 0.79/1.03  thf('57', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.79/1.03      inference('demod', [status(thm)], ['50', '56'])).
% 0.79/1.03  thf('58', plain,
% 0.79/1.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.79/1.03           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.79/1.03      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/1.03  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/1.03      inference('demod', [status(thm)], ['33', '38'])).
% 0.79/1.03  thf('60', plain,
% 0.79/1.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['34', '35'])).
% 0.79/1.03  thf('61', plain,
% 0.79/1.03      (![X17 : $i, X18 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.79/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.79/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/1.03  thf('62', plain,
% 0.79/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X6 @ X4)
% 0.79/1.03          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.79/1.03      inference('simplify', [status(thm)], ['15'])).
% 0.79/1.03  thf('63', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.79/1.03          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['61', '62'])).
% 0.79/1.03  thf('64', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.79/1.03          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['60', '63'])).
% 0.79/1.03  thf('65', plain,
% 0.79/1.03      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X6 @ X5)
% 0.79/1.03          | (r2_hidden @ X6 @ X3)
% 0.79/1.03          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.79/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.79/1.03  thf('66', plain,
% 0.79/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.79/1.03         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.79/1.03      inference('simplify', [status(thm)], ['65'])).
% 0.79/1.03  thf('67', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.79/1.03      inference('clc', [status(thm)], ['64', '66'])).
% 0.79/1.03  thf('68', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['59', '67'])).
% 0.79/1.03  thf('69', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.79/1.03         ~ (r2_hidden @ X3 @ 
% 0.79/1.03            (k4_xboole_0 @ 
% 0.79/1.03             (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.79/1.03             X2))),
% 0.79/1.03      inference('sup-', [status(thm)], ['58', '68'])).
% 0.79/1.03  thf('70', plain,
% 0.79/1.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.79/1.03           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.79/1.03      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/1.03  thf('71', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.79/1.03         ~ (r2_hidden @ X3 @ 
% 0.79/1.03            (k3_xboole_0 @ X1 @ 
% 0.79/1.03             (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.79/1.03      inference('demod', [status(thm)], ['69', '70'])).
% 0.79/1.03  thf('72', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.79/1.03         ~ (r2_hidden @ X3 @ 
% 0.79/1.03            (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.79/1.03      inference('sup-', [status(thm)], ['57', '71'])).
% 0.79/1.03  thf('73', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         ~ (r2_hidden @ X2 @ 
% 0.79/1.03            (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.79/1.03      inference('sup-', [status(thm)], ['47', '72'])).
% 0.79/1.03  thf('74', plain,
% 0.79/1.03      (![X17 : $i, X18 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.79/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.79/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/1.03  thf('75', plain,
% 0.79/1.03      (![X17 : $i, X18 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.79/1.03           = (k3_xboole_0 @ X17 @ X18))),
% 0.79/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/1.03  thf('76', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.79/1.03           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['74', '75'])).
% 0.79/1.03  thf('77', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         ~ (r2_hidden @ X2 @ 
% 0.79/1.03            (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.79/1.03      inference('demod', [status(thm)], ['73', '76'])).
% 0.79/1.03  thf('78', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['52', '53'])).
% 0.79/1.03  thf('79', plain,
% 0.79/1.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.79/1.03           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.79/1.03      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/1.03  thf('80', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.79/1.03           = (k4_xboole_0 @ X0 @ X1))),
% 0.79/1.03      inference('sup+', [status(thm)], ['78', '79'])).
% 0.79/1.03  thf('81', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/1.03      inference('demod', [status(thm)], ['77', '80'])).
% 0.79/1.03  thf('82', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['46', '81'])).
% 0.79/1.03  thf('83', plain,
% 0.79/1.03      (![X11 : $i, X12 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X11 @ X12)
% 0.79/1.03           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/1.03  thf('84', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.79/1.03           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['82', '83'])).
% 0.79/1.03  thf('85', plain,
% 0.79/1.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['36', '37'])).
% 0.79/1.03  thf('86', plain,
% 0.79/1.03      (![X11 : $i, X12 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X11 @ X12)
% 0.79/1.03           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/1.03  thf('87', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['85', '86'])).
% 0.79/1.03  thf('88', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.79/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/1.03  thf('89', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['87', '88'])).
% 0.79/1.03  thf('90', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.79/1.03      inference('demod', [status(thm)], ['84', '89'])).
% 0.79/1.03  thf('91', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.79/1.03          | (r2_hidden @ X0 @ X1))),
% 0.79/1.03      inference('sup+', [status(thm)], ['24', '90'])).
% 0.79/1.03  thf('92', plain,
% 0.79/1.03      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.79/1.03         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.79/1.03      inference('split', [status(esa)], ['3'])).
% 0.79/1.03  thf('93', plain,
% 0.79/1.03      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.79/1.03       ((r2_hidden @ sk_B @ sk_A))),
% 0.79/1.03      inference('split', [status(esa)], ['3'])).
% 0.79/1.03  thf('94', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.79/1.03      inference('sat_resolution*', [status(thm)], ['2', '19', '93'])).
% 0.79/1.03  thf('95', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.79/1.03      inference('simpl_trail', [status(thm)], ['92', '94'])).
% 0.79/1.03  thf('96', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['91', '95'])).
% 0.79/1.03  thf('97', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.79/1.03      inference('simplify', [status(thm)], ['96'])).
% 0.79/1.03  thf('98', plain, ($false), inference('demod', [status(thm)], ['21', '97'])).
% 0.79/1.03  
% 0.79/1.03  % SZS output end Refutation
% 0.79/1.03  
% 0.79/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
