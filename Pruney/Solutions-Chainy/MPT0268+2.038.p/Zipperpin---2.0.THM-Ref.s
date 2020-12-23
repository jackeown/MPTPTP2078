%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XXPDE7P5fH

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:57 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 198 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  652 (1526 expanded)
%              Number of equality atoms :   78 ( 193 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('7',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_xboole_0 @ X52 @ ( k1_tarski @ X51 ) )
        = ( k1_tarski @ X51 ) )
      | ~ ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('8',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 )
        = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['4','12'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      = sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','18'])).

thf('20',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('22',plain,
    ( ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('31',plain,(
    ! [X55: $i,X56: $i] :
      ( ( X56 != X55 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X56 ) @ ( k1_tarski @ X55 ) )
       != ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('32',plain,(
    ! [X55: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X55 ) @ ( k1_tarski @ X55 ) )
     != ( k1_tarski @ X55 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X55: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X55 ) ) ),
    inference(demod,[status(thm)],['32','45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','49'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('51',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X49 ) @ X50 )
      | ( r2_hidden @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('60',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','48','59'])).

thf('61',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['58','60'])).

thf('62',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['50','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XXPDE7P5fH
% 0.16/0.37  % Computer   : n025.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:45:36 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 133 iterations in 0.073s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(t65_zfmisc_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.36/0.56       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i]:
% 0.36/0.56        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.36/0.56          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.36/0.56        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.36/0.56       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.36/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf(t92_xboole_1, axiom,
% 0.36/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.56  thf('4', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ sk_A)
% 0.36/0.56        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['5'])).
% 0.36/0.56  thf(l31_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.36/0.56       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (![X51 : $i, X52 : $i]:
% 0.36/0.56         (((k3_xboole_0 @ X52 @ (k1_tarski @ X51)) = (k1_tarski @ X51))
% 0.36/0.56          | ~ (r2_hidden @ X51 @ X52))),
% 0.36/0.56      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      ((((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.56  thf(t100_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X5 : $i, X6 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.36/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56          = (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf(t91_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.36/0.56           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ X0)
% 0.36/0.56            = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0))))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ 
% 0.36/0.56          (k1_tarski @ sk_B)) = (k5_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['4', '12'])).
% 0.36/0.56  thf(commutativity_k5_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.56  thf(t5_boole, axiom,
% 0.36/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.56  thf('17', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.56  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      ((((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.36/0.56          (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))) = (sk_A)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['13', '14', '15', '18'])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      ((((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (sk_A)))
% 0.36/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.36/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['3', '19'])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      ((((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.36/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.36/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.56  thf('23', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.36/0.56           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.36/0.56  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      ((((k1_tarski @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A)))
% 0.36/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.36/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['22', '27'])).
% 0.36/0.56  thf('29', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.36/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.36/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.56  thf(t20_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.56         ( k1_tarski @ A ) ) <=>
% 0.36/0.56       ( ( A ) != ( B ) ) ))).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X55 : $i, X56 : $i]:
% 0.36/0.56         (((X56) != (X55))
% 0.36/0.56          | ((k4_xboole_0 @ (k1_tarski @ X56) @ (k1_tarski @ X55))
% 0.36/0.56              != (k1_tarski @ X56)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X55 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ (k1_tarski @ X55) @ (k1_tarski @ X55))
% 0.36/0.56           != (k1_tarski @ X55))),
% 0.36/0.56      inference('simplify', [status(thm)], ['31'])).
% 0.36/0.56  thf(idempotence_k2_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.56  thf('33', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.36/0.56  thf(t95_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k3_xboole_0 @ A @ B ) =
% 0.36/0.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (![X19 : $i, X20 : $i]:
% 0.36/0.56         ((k3_xboole_0 @ X19 @ X20)
% 0.36/0.56           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.36/0.56              (k2_xboole_0 @ X19 @ X20)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X19 : $i, X20 : $i]:
% 0.36/0.56         ((k3_xboole_0 @ X19 @ X20)
% 0.36/0.56           = (k5_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 0.36/0.56              (k5_xboole_0 @ X19 @ X20)))),
% 0.36/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k3_xboole_0 @ X0 @ X0)
% 0.36/0.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['33', '36'])).
% 0.36/0.56  thf('38', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.56  thf('40', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.56  thf('41', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (![X5 : $i, X6 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.36/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.56  thf('43', plain,
% 0.36/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['41', '42'])).
% 0.36/0.56  thf('44', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.56  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('46', plain, (![X55 : $i]: ((k1_xboole_0) != (k1_tarski @ X55))),
% 0.36/0.56      inference('demod', [status(thm)], ['32', '45'])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.36/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.36/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['30', '46'])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.36/0.56       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.36/0.56      inference('simplify', [status(thm)], ['47'])).
% 0.36/0.56  thf('49', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['2', '48'])).
% 0.36/0.56  thf('50', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['1', '49'])).
% 0.36/0.56  thf(l27_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (![X49 : $i, X50 : $i]:
% 0.36/0.56         ((r1_xboole_0 @ (k1_tarski @ X49) @ X50) | (r2_hidden @ X49 @ X50))),
% 0.36/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.36/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i]:
% 0.36/0.56         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.36/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.56  thf(t88_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_xboole_0 @ A @ B ) =>
% 0.36/0.56       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i]:
% 0.36/0.56         (((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14) = (X13))
% 0.36/0.56          | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.36/0.56  thf(t40_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 0.36/0.56           = (k4_xboole_0 @ X7 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.36/0.56  thf('56', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i]:
% 0.36/0.56         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.36/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.56  thf('57', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((r2_hidden @ X0 @ X1)
% 0.36/0.56          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['53', '56'])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.36/0.56         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.36/0.56      inference('split', [status(esa)], ['5'])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.36/0.56       ((r2_hidden @ sk_B @ sk_A))),
% 0.36/0.56      inference('split', [status(esa)], ['5'])).
% 0.36/0.56  thf('60', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['2', '48', '59'])).
% 0.36/0.56  thf('61', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['58', '60'])).
% 0.36/0.56  thf('62', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '61'])).
% 0.36/0.56  thf('63', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.36/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.36/0.56  thf('64', plain, ($false), inference('demod', [status(thm)], ['50', '63'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
