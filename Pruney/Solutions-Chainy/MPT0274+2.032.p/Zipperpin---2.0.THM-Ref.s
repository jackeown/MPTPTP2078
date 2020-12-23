%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ptnnvpDyS2

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:36 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 301 expanded)
%              Number of leaves         :   28 (  93 expanded)
%              Depth                    :   18
%              Number of atoms          :  910 (2851 expanded)
%              Number of equality atoms :   87 ( 270 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X32: $i,X34: $i] :
      ( ( r1_xboole_0 @ X32 @ X34 )
      | ( ( k4_xboole_0 @ X32 @ X34 )
       != X32 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,
    ( ( ( ( k2_tarski @ sk_A @ sk_B )
       != ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('9',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X49 @ X50 ) @ X51 )
      | ~ ( r2_hidden @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('14',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( r2_hidden @ X52 @ X53 )
      | ( r1_xboole_0 @ ( k2_tarski @ X52 @ X54 ) @ X53 )
      | ( r2_hidden @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X40 != X39 )
      | ( r2_hidden @ X40 @ X41 )
      | ( X41
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X39: $i] :
      ( r2_hidden @ X39 @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t70_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('20',plain,(
    ! [X65: $i,X67: $i,X68: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X65 @ X67 ) @ X68 )
        = ( k1_tarski @ X65 ) )
      | ( X65 != X67 )
      | ( r2_hidden @ X65 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t70_zfmisc_1])).

thf('21',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r2_hidden @ X67 @ X68 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X67 @ X67 ) @ X68 )
        = ( k1_tarski @ X67 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('22',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_tarski @ X44 @ X45 )
      = ( k2_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r2_hidden @ X67 @ X68 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X67 ) @ X68 )
        = ( k1_tarski @ X67 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_tarski @ X44 @ X45 )
      = ( k2_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('28',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( X58 != X60 )
      | ~ ( r2_hidden @ X58 @ ( k4_xboole_0 @ X59 @ ( k1_tarski @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('29',plain,(
    ! [X59: $i,X60: $i] :
      ~ ( r2_hidden @ X60 @ ( k4_xboole_0 @ X59 @ ( k1_tarski @ X60 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf(t60_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( ( r2_hidden @ C @ B )
          & ( A != C ) )
        | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k1_tarski @ A ) ) ) ) )).

thf('36',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X55 @ X56 )
      | ( X55 != X57 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X55 @ X57 ) @ X56 )
        = ( k1_tarski @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t60_zfmisc_1])).

thf('37',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ X57 @ X57 ) @ X56 )
        = ( k1_tarski @ X57 ) )
      | ~ ( r2_hidden @ X57 @ X56 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('39',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X57 ) @ X56 )
        = ( k1_tarski @ X57 ) )
      | ~ ( r2_hidden @ X57 @ X56 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_C_2 )
      = ( k1_tarski @ sk_B ) )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_C_2 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_C_2 )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['42','53'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k4_xboole_0 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('56',plain,
    ( ( ( k2_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_B ) )
      = ( k5_xboole_0 @ sk_C_2 @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('58',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('61',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_B ) )
      = sk_C_2 )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('68',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','69'])).

thf('71',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('72',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','11','70','71'])).

thf('73',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','72'])).

thf('74',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C_2 )
    | ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['76'])).

thf('79',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','11','70','71','78'])).

thf('80',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,(
    r2_hidden @ sk_A @ sk_C_2 ),
    inference(clc,[status(thm)],['75','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['13','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ptnnvpDyS2
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:12:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.39/1.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.39/1.58  % Solved by: fo/fo7.sh
% 1.39/1.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.39/1.58  % done 3052 iterations in 1.138s
% 1.39/1.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.39/1.58  % SZS output start Refutation
% 1.39/1.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.39/1.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.39/1.58  thf(sk_A_type, type, sk_A: $i).
% 1.39/1.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.39/1.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.39/1.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.39/1.58  thf(sk_B_type, type, sk_B: $i).
% 1.39/1.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.39/1.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.39/1.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.39/1.58  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.39/1.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.39/1.58  thf(t72_zfmisc_1, conjecture,
% 1.39/1.58    (![A:$i,B:$i,C:$i]:
% 1.39/1.58     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.39/1.58       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 1.39/1.58  thf(zf_stmt_0, negated_conjecture,
% 1.39/1.58    (~( ![A:$i,B:$i,C:$i]:
% 1.39/1.58        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.39/1.58          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 1.39/1.58    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 1.39/1.58  thf('0', plain,
% 1.39/1.58      ((~ (r2_hidden @ sk_A @ sk_C_2)
% 1.39/1.58        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58            = (k2_tarski @ sk_A @ sk_B)))),
% 1.39/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.58  thf('1', plain,
% 1.39/1.58      ((~ (r2_hidden @ sk_A @ sk_C_2)) <= (~ ((r2_hidden @ sk_A @ sk_C_2)))),
% 1.39/1.58      inference('split', [status(esa)], ['0'])).
% 1.39/1.58  thf('2', plain,
% 1.39/1.58      (~ ((r2_hidden @ sk_A @ sk_C_2)) | 
% 1.39/1.58       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k2_tarski @ sk_A @ sk_B)))),
% 1.39/1.58      inference('split', [status(esa)], ['0'])).
% 1.39/1.58  thf('3', plain,
% 1.39/1.58      (((r2_hidden @ sk_B @ sk_C_2)
% 1.39/1.58        | (r2_hidden @ sk_A @ sk_C_2)
% 1.39/1.58        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58            != (k2_tarski @ sk_A @ sk_B)))),
% 1.39/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.58  thf('4', plain,
% 1.39/1.58      (((r2_hidden @ sk_A @ sk_C_2)) <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 1.39/1.58      inference('split', [status(esa)], ['3'])).
% 1.39/1.58  thf('5', plain,
% 1.39/1.58      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k2_tarski @ sk_A @ sk_B)))
% 1.39/1.58         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58                = (k2_tarski @ sk_A @ sk_B))))),
% 1.39/1.58      inference('split', [status(esa)], ['0'])).
% 1.39/1.58  thf(t83_xboole_1, axiom,
% 1.39/1.58    (![A:$i,B:$i]:
% 1.39/1.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.39/1.58  thf('6', plain,
% 1.39/1.58      (![X32 : $i, X34 : $i]:
% 1.39/1.58         ((r1_xboole_0 @ X32 @ X34) | ((k4_xboole_0 @ X32 @ X34) != (X32)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.39/1.58  thf('7', plain,
% 1.39/1.58      (((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 1.39/1.58         | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)))
% 1.39/1.58         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58                = (k2_tarski @ sk_A @ sk_B))))),
% 1.39/1.58      inference('sup-', [status(thm)], ['5', '6'])).
% 1.39/1.58  thf('8', plain,
% 1.39/1.58      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))
% 1.39/1.58         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58                = (k2_tarski @ sk_A @ sk_B))))),
% 1.39/1.58      inference('simplify', [status(thm)], ['7'])).
% 1.39/1.58  thf(t55_zfmisc_1, axiom,
% 1.39/1.58    (![A:$i,B:$i,C:$i]:
% 1.39/1.58     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 1.39/1.58  thf('9', plain,
% 1.39/1.58      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.39/1.58         (~ (r1_xboole_0 @ (k2_tarski @ X49 @ X50) @ X51)
% 1.39/1.58          | ~ (r2_hidden @ X49 @ X51))),
% 1.39/1.58      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 1.39/1.58  thf('10', plain,
% 1.39/1.58      ((~ (r2_hidden @ sk_A @ sk_C_2))
% 1.39/1.58         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58                = (k2_tarski @ sk_A @ sk_B))))),
% 1.39/1.58      inference('sup-', [status(thm)], ['8', '9'])).
% 1.39/1.58  thf('11', plain,
% 1.39/1.58      (~ ((r2_hidden @ sk_A @ sk_C_2)) | 
% 1.39/1.58       ~
% 1.39/1.58       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k2_tarski @ sk_A @ sk_B)))),
% 1.39/1.58      inference('sup-', [status(thm)], ['4', '10'])).
% 1.39/1.58  thf('12', plain, (~ ((r2_hidden @ sk_A @ sk_C_2))),
% 1.39/1.58      inference('sat_resolution*', [status(thm)], ['2', '11'])).
% 1.39/1.58  thf('13', plain, (~ (r2_hidden @ sk_A @ sk_C_2)),
% 1.39/1.58      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 1.39/1.58  thf(t57_zfmisc_1, axiom,
% 1.39/1.58    (![A:$i,B:$i,C:$i]:
% 1.39/1.58     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 1.39/1.58          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 1.39/1.58  thf('14', plain,
% 1.39/1.58      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.39/1.58         ((r2_hidden @ X52 @ X53)
% 1.39/1.58          | (r1_xboole_0 @ (k2_tarski @ X52 @ X54) @ X53)
% 1.39/1.58          | (r2_hidden @ X54 @ X53))),
% 1.39/1.58      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 1.39/1.58  thf('15', plain,
% 1.39/1.58      (![X32 : $i, X33 : $i]:
% 1.39/1.58         (((k4_xboole_0 @ X32 @ X33) = (X32)) | ~ (r1_xboole_0 @ X32 @ X33))),
% 1.39/1.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.39/1.58  thf('16', plain,
% 1.39/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.58         ((r2_hidden @ X1 @ X0)
% 1.39/1.58          | (r2_hidden @ X2 @ X0)
% 1.39/1.58          | ((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1)))),
% 1.39/1.58      inference('sup-', [status(thm)], ['14', '15'])).
% 1.39/1.58  thf('17', plain,
% 1.39/1.58      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          != (k2_tarski @ sk_A @ sk_B)))
% 1.39/1.58         <= (~
% 1.39/1.58             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58                = (k2_tarski @ sk_A @ sk_B))))),
% 1.39/1.58      inference('split', [status(esa)], ['3'])).
% 1.39/1.58  thf(d1_tarski, axiom,
% 1.39/1.58    (![A:$i,B:$i]:
% 1.39/1.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.39/1.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.39/1.58  thf('18', plain,
% 1.39/1.58      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.39/1.58         (((X40) != (X39))
% 1.39/1.58          | (r2_hidden @ X40 @ X41)
% 1.39/1.58          | ((X41) != (k1_tarski @ X39)))),
% 1.39/1.58      inference('cnf', [status(esa)], [d1_tarski])).
% 1.39/1.58  thf('19', plain, (![X39 : $i]: (r2_hidden @ X39 @ (k1_tarski @ X39))),
% 1.39/1.58      inference('simplify', [status(thm)], ['18'])).
% 1.39/1.58  thf(t70_zfmisc_1, axiom,
% 1.39/1.58    (![A:$i,B:$i,C:$i]:
% 1.39/1.58     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 1.39/1.58       ( ( ~( r2_hidden @ A @ C ) ) & 
% 1.39/1.58         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 1.39/1.58  thf('20', plain,
% 1.39/1.58      (![X65 : $i, X67 : $i, X68 : $i]:
% 1.39/1.58         (((k4_xboole_0 @ (k2_tarski @ X65 @ X67) @ X68) = (k1_tarski @ X65))
% 1.39/1.58          | ((X65) != (X67))
% 1.39/1.58          | (r2_hidden @ X65 @ X68))),
% 1.39/1.58      inference('cnf', [status(esa)], [t70_zfmisc_1])).
% 1.39/1.58  thf('21', plain,
% 1.39/1.58      (![X67 : $i, X68 : $i]:
% 1.39/1.58         ((r2_hidden @ X67 @ X68)
% 1.39/1.58          | ((k4_xboole_0 @ (k2_tarski @ X67 @ X67) @ X68) = (k1_tarski @ X67)))),
% 1.39/1.58      inference('simplify', [status(thm)], ['20'])).
% 1.39/1.58  thf(t41_enumset1, axiom,
% 1.39/1.58    (![A:$i,B:$i]:
% 1.39/1.58     ( ( k2_tarski @ A @ B ) =
% 1.39/1.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 1.39/1.58  thf('22', plain,
% 1.39/1.58      (![X44 : $i, X45 : $i]:
% 1.39/1.58         ((k2_tarski @ X44 @ X45)
% 1.39/1.58           = (k2_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X45)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.39/1.58  thf(idempotence_k2_xboole_0, axiom,
% 1.39/1.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.39/1.58  thf('23', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.39/1.58      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.39/1.58  thf('24', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['22', '23'])).
% 1.39/1.58  thf('25', plain,
% 1.39/1.58      (![X67 : $i, X68 : $i]:
% 1.39/1.58         ((r2_hidden @ X67 @ X68)
% 1.39/1.58          | ((k4_xboole_0 @ (k1_tarski @ X67) @ X68) = (k1_tarski @ X67)))),
% 1.39/1.58      inference('demod', [status(thm)], ['21', '24'])).
% 1.39/1.58  thf('26', plain,
% 1.39/1.58      (![X44 : $i, X45 : $i]:
% 1.39/1.58         ((k2_tarski @ X44 @ X45)
% 1.39/1.58           = (k2_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X45)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.39/1.58  thf(t41_xboole_1, axiom,
% 1.39/1.58    (![A:$i,B:$i,C:$i]:
% 1.39/1.58     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.39/1.58       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.39/1.58  thf('27', plain,
% 1.39/1.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.39/1.58         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 1.39/1.58           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.39/1.58  thf(t64_zfmisc_1, axiom,
% 1.39/1.58    (![A:$i,B:$i,C:$i]:
% 1.39/1.58     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.39/1.58       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.39/1.58  thf('28', plain,
% 1.39/1.58      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.39/1.58         (((X58) != (X60))
% 1.39/1.58          | ~ (r2_hidden @ X58 @ (k4_xboole_0 @ X59 @ (k1_tarski @ X60))))),
% 1.39/1.58      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.39/1.58  thf('29', plain,
% 1.39/1.58      (![X59 : $i, X60 : $i]:
% 1.39/1.58         ~ (r2_hidden @ X60 @ (k4_xboole_0 @ X59 @ (k1_tarski @ X60)))),
% 1.39/1.58      inference('simplify', [status(thm)], ['28'])).
% 1.39/1.58  thf('30', plain,
% 1.39/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.58         ~ (r2_hidden @ X0 @ 
% 1.39/1.58            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.39/1.58      inference('sup-', [status(thm)], ['27', '29'])).
% 1.39/1.58  thf('31', plain,
% 1.39/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.58         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 1.39/1.58      inference('sup-', [status(thm)], ['26', '30'])).
% 1.39/1.58  thf('32', plain,
% 1.39/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.58         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.39/1.58          | (r2_hidden @ X0 @ (k2_tarski @ X2 @ X1)))),
% 1.39/1.58      inference('sup-', [status(thm)], ['25', '31'])).
% 1.39/1.58  thf('33', plain,
% 1.39/1.58      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.39/1.58      inference('sup-', [status(thm)], ['19', '32'])).
% 1.39/1.58  thf('34', plain,
% 1.39/1.58      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k2_tarski @ sk_A @ sk_B)))
% 1.39/1.58         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58                = (k2_tarski @ sk_A @ sk_B))))),
% 1.39/1.58      inference('split', [status(esa)], ['0'])).
% 1.39/1.58  thf('35', plain,
% 1.39/1.58      (((r2_hidden @ sk_B @ sk_C_2)) <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('split', [status(esa)], ['3'])).
% 1.39/1.58  thf(t60_zfmisc_1, axiom,
% 1.39/1.58    (![A:$i,B:$i,C:$i]:
% 1.39/1.58     ( ( r2_hidden @ A @ B ) =>
% 1.39/1.58       ( ( ( r2_hidden @ C @ B ) & ( ( A ) != ( C ) ) ) | 
% 1.39/1.58         ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k1_tarski @ A ) ) ) ))).
% 1.39/1.58  thf('36', plain,
% 1.39/1.58      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.39/1.58         (~ (r2_hidden @ X55 @ X56)
% 1.39/1.58          | ((X55) != (X57))
% 1.39/1.58          | ((k3_xboole_0 @ (k2_tarski @ X55 @ X57) @ X56) = (k1_tarski @ X55)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t60_zfmisc_1])).
% 1.39/1.58  thf('37', plain,
% 1.39/1.58      (![X56 : $i, X57 : $i]:
% 1.39/1.58         (((k3_xboole_0 @ (k2_tarski @ X57 @ X57) @ X56) = (k1_tarski @ X57))
% 1.39/1.58          | ~ (r2_hidden @ X57 @ X56))),
% 1.39/1.58      inference('simplify', [status(thm)], ['36'])).
% 1.39/1.58  thf('38', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['22', '23'])).
% 1.39/1.58  thf('39', plain,
% 1.39/1.58      (![X56 : $i, X57 : $i]:
% 1.39/1.58         (((k3_xboole_0 @ (k1_tarski @ X57) @ X56) = (k1_tarski @ X57))
% 1.39/1.58          | ~ (r2_hidden @ X57 @ X56))),
% 1.39/1.58      inference('demod', [status(thm)], ['37', '38'])).
% 1.39/1.58  thf('40', plain,
% 1.39/1.58      ((((k3_xboole_0 @ (k1_tarski @ sk_B) @ sk_C_2) = (k1_tarski @ sk_B)))
% 1.39/1.58         <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('sup-', [status(thm)], ['35', '39'])).
% 1.39/1.58  thf(t100_xboole_1, axiom,
% 1.39/1.58    (![A:$i,B:$i]:
% 1.39/1.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.39/1.58  thf('41', plain,
% 1.39/1.58      (![X17 : $i, X18 : $i]:
% 1.39/1.58         ((k4_xboole_0 @ X17 @ X18)
% 1.39/1.58           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.39/1.58  thf('42', plain,
% 1.39/1.58      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 1.39/1.58         <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('sup+', [status(thm)], ['40', '41'])).
% 1.39/1.58  thf('43', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.39/1.58      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.39/1.58  thf(t46_xboole_1, axiom,
% 1.39/1.58    (![A:$i,B:$i]:
% 1.39/1.58     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.39/1.58  thf('44', plain,
% 1.39/1.58      (![X25 : $i, X26 : $i]:
% 1.39/1.58         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 1.39/1.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.39/1.58  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['43', '44'])).
% 1.39/1.58  thf(t48_xboole_1, axiom,
% 1.39/1.58    (![A:$i,B:$i]:
% 1.39/1.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.39/1.58  thf('46', plain,
% 1.39/1.58      (![X29 : $i, X30 : $i]:
% 1.39/1.58         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 1.39/1.58           = (k3_xboole_0 @ X29 @ X30))),
% 1.39/1.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.39/1.58  thf('47', plain,
% 1.39/1.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['45', '46'])).
% 1.39/1.58  thf(t3_boole, axiom,
% 1.39/1.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.39/1.58  thf('48', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.39/1.58      inference('cnf', [status(esa)], [t3_boole])).
% 1.39/1.58  thf('49', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.39/1.58      inference('demod', [status(thm)], ['47', '48'])).
% 1.39/1.58  thf('50', plain,
% 1.39/1.58      (![X17 : $i, X18 : $i]:
% 1.39/1.58         ((k4_xboole_0 @ X17 @ X18)
% 1.39/1.58           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.39/1.58  thf('51', plain,
% 1.39/1.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['49', '50'])).
% 1.39/1.58  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['43', '44'])).
% 1.39/1.58  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['51', '52'])).
% 1.39/1.58  thf('54', plain,
% 1.39/1.58      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_C_2) = (k1_xboole_0)))
% 1.39/1.58         <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('demod', [status(thm)], ['42', '53'])).
% 1.39/1.58  thf(t98_xboole_1, axiom,
% 1.39/1.58    (![A:$i,B:$i]:
% 1.39/1.58     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.39/1.58  thf('55', plain,
% 1.39/1.58      (![X37 : $i, X38 : $i]:
% 1.39/1.58         ((k2_xboole_0 @ X37 @ X38)
% 1.39/1.58           = (k5_xboole_0 @ X37 @ (k4_xboole_0 @ X38 @ X37)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.39/1.58  thf('56', plain,
% 1.39/1.58      ((((k2_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_B))
% 1.39/1.58          = (k5_xboole_0 @ sk_C_2 @ k1_xboole_0)))
% 1.39/1.58         <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('sup+', [status(thm)], ['54', '55'])).
% 1.39/1.58  thf('57', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.39/1.58      inference('cnf', [status(esa)], [t3_boole])).
% 1.39/1.58  thf('58', plain,
% 1.39/1.58      (![X29 : $i, X30 : $i]:
% 1.39/1.58         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 1.39/1.58           = (k3_xboole_0 @ X29 @ X30))),
% 1.39/1.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.39/1.58  thf('59', plain,
% 1.39/1.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['57', '58'])).
% 1.39/1.58  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['43', '44'])).
% 1.39/1.58  thf('61', plain,
% 1.39/1.58      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.39/1.58      inference('demod', [status(thm)], ['59', '60'])).
% 1.39/1.58  thf('62', plain,
% 1.39/1.58      (![X17 : $i, X18 : $i]:
% 1.39/1.58         ((k4_xboole_0 @ X17 @ X18)
% 1.39/1.58           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.39/1.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.39/1.58  thf('63', plain,
% 1.39/1.58      (![X0 : $i]:
% 1.39/1.58         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['61', '62'])).
% 1.39/1.58  thf('64', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.39/1.58      inference('cnf', [status(esa)], [t3_boole])).
% 1.39/1.58  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.39/1.58      inference('sup+', [status(thm)], ['63', '64'])).
% 1.39/1.58  thf('66', plain,
% 1.39/1.58      ((((k2_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_B)) = (sk_C_2)))
% 1.39/1.58         <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('demod', [status(thm)], ['56', '65'])).
% 1.39/1.58  thf('67', plain,
% 1.39/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.58         ~ (r2_hidden @ X0 @ 
% 1.39/1.58            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.39/1.58      inference('sup-', [status(thm)], ['27', '29'])).
% 1.39/1.58  thf('68', plain,
% 1.39/1.58      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2)))
% 1.39/1.58         <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('sup-', [status(thm)], ['66', '67'])).
% 1.39/1.58  thf('69', plain,
% 1.39/1.58      ((~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))
% 1.39/1.58         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58                = (k2_tarski @ sk_A @ sk_B))) & 
% 1.39/1.58             ((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('sup-', [status(thm)], ['34', '68'])).
% 1.39/1.58  thf('70', plain,
% 1.39/1.58      (~ ((r2_hidden @ sk_B @ sk_C_2)) | 
% 1.39/1.58       ~
% 1.39/1.58       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k2_tarski @ sk_A @ sk_B)))),
% 1.39/1.58      inference('sup-', [status(thm)], ['33', '69'])).
% 1.39/1.58  thf('71', plain,
% 1.39/1.58      (~
% 1.39/1.58       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k2_tarski @ sk_A @ sk_B))) | 
% 1.39/1.58       ((r2_hidden @ sk_B @ sk_C_2)) | ((r2_hidden @ sk_A @ sk_C_2))),
% 1.39/1.58      inference('split', [status(esa)], ['3'])).
% 1.39/1.58  thf('72', plain,
% 1.39/1.58      (~
% 1.39/1.58       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k2_tarski @ sk_A @ sk_B)))),
% 1.39/1.58      inference('sat_resolution*', [status(thm)], ['2', '11', '70', '71'])).
% 1.39/1.58  thf('73', plain,
% 1.39/1.58      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58         != (k2_tarski @ sk_A @ sk_B))),
% 1.39/1.58      inference('simpl_trail', [status(thm)], ['17', '72'])).
% 1.39/1.58  thf('74', plain,
% 1.39/1.58      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 1.39/1.58        | (r2_hidden @ sk_A @ sk_C_2)
% 1.39/1.58        | (r2_hidden @ sk_B @ sk_C_2))),
% 1.39/1.58      inference('sup-', [status(thm)], ['16', '73'])).
% 1.39/1.58  thf('75', plain,
% 1.39/1.58      (((r2_hidden @ sk_B @ sk_C_2) | (r2_hidden @ sk_A @ sk_C_2))),
% 1.39/1.58      inference('simplify', [status(thm)], ['74'])).
% 1.39/1.58  thf('76', plain,
% 1.39/1.58      ((~ (r2_hidden @ sk_B @ sk_C_2)
% 1.39/1.58        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58            = (k2_tarski @ sk_A @ sk_B)))),
% 1.39/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.58  thf('77', plain,
% 1.39/1.58      ((~ (r2_hidden @ sk_B @ sk_C_2)) <= (~ ((r2_hidden @ sk_B @ sk_C_2)))),
% 1.39/1.58      inference('split', [status(esa)], ['76'])).
% 1.39/1.58  thf('78', plain,
% 1.39/1.58      (~ ((r2_hidden @ sk_B @ sk_C_2)) | 
% 1.39/1.58       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 1.39/1.58          = (k2_tarski @ sk_A @ sk_B)))),
% 1.39/1.58      inference('split', [status(esa)], ['76'])).
% 1.39/1.58  thf('79', plain, (~ ((r2_hidden @ sk_B @ sk_C_2))),
% 1.39/1.58      inference('sat_resolution*', [status(thm)], ['2', '11', '70', '71', '78'])).
% 1.39/1.58  thf('80', plain, (~ (r2_hidden @ sk_B @ sk_C_2)),
% 1.39/1.58      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 1.39/1.58  thf('81', plain, ((r2_hidden @ sk_A @ sk_C_2)),
% 1.39/1.58      inference('clc', [status(thm)], ['75', '80'])).
% 1.39/1.58  thf('82', plain, ($false), inference('demod', [status(thm)], ['13', '81'])).
% 1.39/1.58  
% 1.39/1.58  % SZS output end Refutation
% 1.39/1.58  
% 1.39/1.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
