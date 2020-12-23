%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0243+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mujvPwEBLb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 4.15s
% Output     : Refutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 183 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  588 (1619 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_8_type,type,(
    sk_C_8: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t38_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ C ) )
    <=> ( ( r2_hidden @ ( A @ C ) )
        & ( r2_hidden @ ( B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ C ) )
      <=> ( ( r2_hidden @ ( A @ C ) )
          & ( r2_hidden @ ( B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) )
    | ~ ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) )
    | ~ ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) )
   <= ~ ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X441: $i,X442: $i,X443: $i,X444: $i] :
      ( ( X442 != X444 )
      | ( r2_hidden @ ( X442 @ X443 ) )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X441: $i,X444: $i] :
      ( r2_hidden @ ( X444 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) )
    | ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) )
   <= ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( X0 @ sk_C_8 ) )
        | ~ ( r2_hidden @ ( X0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) )
   <= ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) )
   <= ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) )
   <= ~ ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) )
    | ~ ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X441: $i,X442: $i,X443: $i,X444: $i] :
      ( ( X442 != X441 )
      | ( r2_hidden @ ( X442 @ X443 ) )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X441: $i,X444: $i] :
      ( r2_hidden @ ( X441 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( X0 @ sk_C_8 ) )
        | ~ ( r2_hidden @ ( X0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) )
   <= ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) )
   <= ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) )
   <= ~ ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) )
    | ~ ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) )
    | ~ ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) )
    | ~ ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference('sat_resolution*',[status(thm)],['10','16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) )
    | ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) )
   <= ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['20'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('22',plain,(
    ! [X993: $i,X995: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X993 @ X995 ) )
      | ~ ( r2_hidden @ ( X993 @ X995 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_2 @ sk_C_8 ) )
   <= ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('24',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_2 @ sk_C_8 ) )
      = ( k1_tarski @ sk_B_2 ) )
   <= ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ ( sk_C_8 @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k1_tarski @ sk_B_2 ) )
   <= ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('28',plain,(
    ! [X192: $i,X193: $i] :
      ( ( k2_xboole_0 @ ( X192 @ ( k3_xboole_0 @ ( X192 @ X193 ) ) ) )
      = X192 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('29',plain,
    ( ( ( k2_xboole_0 @ ( sk_C_8 @ ( k1_tarski @ sk_B_2 ) ) )
      = sk_C_8 )
   <= ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_8 ) )
    | ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('31',plain,(
    r2_hidden @ ( sk_B_2 @ sk_C_8 ) ),
    inference('sat_resolution*',[status(thm)],['10','16','17','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ ( sk_C_8 @ ( k1_tarski @ sk_B_2 ) ) )
    = sk_C_8 ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X18 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('36',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_A_2 @ ( k2_xboole_0 @ ( X0 @ sk_C_8 ) ) ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_8 @ X0 ) ) ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) ) ),
    inference('sup+',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X993: $i,X995: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X993 @ X995 ) )
      | ~ ( r2_hidden @ ( X993 @ X995 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tarski @ sk_A_2 @ ( k2_xboole_0 @ ( sk_C_8 @ X0 ) ) ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('41',plain,(
    ! [X419: $i,X420: $i,X421: $i] :
      ( ~ ( r1_tarski @ ( X419 @ X420 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ ( X419 @ X421 ) @ ( k2_xboole_0 @ ( X420 @ X421 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('42',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ X1 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_C_8 @ X0 ) @ X1 ) ) ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('43',plain,(
    ! [X272: $i,X273: $i,X274: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X272 @ X273 ) @ X274 ) )
      = ( k2_xboole_0 @ ( X272 @ ( k2_xboole_0 @ ( X273 @ X274 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ X1 ) @ ( k2_xboole_0 @ ( sk_C_8 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_8 ) )
    | ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('46',plain,(
    r2_hidden @ ( sk_A_2 @ sk_C_8 ) ),
    inference('sat_resolution*',[status(thm)],['10','16','17','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ X1 ) @ ( k2_xboole_0 @ ( sk_C_8 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['44','46'])).

thf('48',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_xboole_0 @ ( sk_C_8 @ sk_C_8 ) ) ) ),
    inference('sup+',[status(thm)],['32','47'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('49',plain,(
    ! [X702: $i,X703: $i] :
      ( ( k2_tarski @ ( X702 @ X703 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X702 @ ( k1_tarski @ X703 ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 @ ( k1_tarski @ X1 ) ) )
      = ( k2_tarski @ ( X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_tarski @ ( B @ A ) ) ) )).

thf('52',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('53',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('54',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_8 ) ),
    inference(demod,[status(thm)],['48','51','52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['19','54'])).

%------------------------------------------------------------------------------
