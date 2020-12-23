%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SunDisyUHZ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:03 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 178 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  692 (1440 expanded)
%              Number of equality atoms :   51 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_subset_1 @ X41 @ X42 )
        = ( k4_xboole_0 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_xboole_0 @ X26 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('17',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['15','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_xboole_0 @ X24 @ ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ X39 )
      | ( r2_hidden @ X38 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X43: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('27',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( r1_tarski @ X36 @ X34 )
      | ( X35
       != ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ X36 @ X34 )
      | ~ ( r2_hidden @ X36 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['27','29'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X32: $i] :
      ( ( k5_xboole_0 @ X32 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X32: $i] :
      ( ( k5_xboole_0 @ X32 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ X31 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','48','49','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['14','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SunDisyUHZ
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 1412 iterations in 0.504s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(t44_subset_1, conjecture,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ![C:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.77/0.96             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i,B:$i]:
% 0.77/0.96        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96          ( ![C:$i]:
% 0.77/0.96            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.77/0.96                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.77/0.96  thf('0', plain,
% 0.77/0.96      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.77/0.96        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.77/0.96       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(d5_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      (![X41 : $i, X42 : $i]:
% 0.77/0.96         (((k3_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))
% 0.77/0.96          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      (((r1_tarski @ sk_B @ sk_C_1)
% 0.77/0.96        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.96      inference('split', [status(esa)], ['6'])).
% 0.77/0.96  thf(t85_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.77/0.96  thf('8', plain,
% 0.77/0.96      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X26 @ X27)
% 0.77/0.96          | (r1_xboole_0 @ X26 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.77/0.96  thf('9', plain,
% 0.77/0.96      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.77/0.96         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.77/0.96         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['5', '9'])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.77/0.96         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('12', plain,
% 0.77/0.96      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.77/0.96       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/0.96  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.96      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.77/0.96  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.77/0.96      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.77/0.96         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.77/0.96      inference('split', [status(esa)], ['6'])).
% 0.77/0.96  thf('16', plain,
% 0.77/0.96      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.77/0.96       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.96      inference('split', [status(esa)], ['6'])).
% 0.77/0.96  thf('17', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.77/0.96      inference('sat_resolution*', [status(thm)], ['2', '12', '16'])).
% 0.77/0.96  thf('18', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.77/0.96      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/0.96  thf(t81_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.77/0.96       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.77/0.96  thf('20', plain,
% 0.77/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.77/0.96         ((r1_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.77/0.96          | ~ (r1_xboole_0 @ X24 @ (k4_xboole_0 @ X23 @ X25)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.77/0.96  thf('21', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.77/0.96          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.77/0.96  thf('22', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['18', '21'])).
% 0.77/0.96  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(d2_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( v1_xboole_0 @ A ) =>
% 0.77/0.96         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.77/0.96       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.77/0.96         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      (![X38 : $i, X39 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X38 @ X39)
% 0.77/0.96          | (r2_hidden @ X38 @ X39)
% 0.77/0.96          | (v1_xboole_0 @ X39))),
% 0.77/0.96      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.77/0.96  thf('25', plain,
% 0.77/0.96      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.77/0.96        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.96  thf(fc1_subset_1, axiom,
% 0.77/0.96    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.77/0.96  thf('26', plain, (![X43 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.77/0.96  thf('27', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.96      inference('clc', [status(thm)], ['25', '26'])).
% 0.77/0.96  thf(d1_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.77/0.96       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X36 @ X35)
% 0.77/0.96          | (r1_tarski @ X36 @ X34)
% 0.77/0.96          | ((X35) != (k1_zfmisc_1 @ X34)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.77/0.96  thf('29', plain,
% 0.77/0.96      (![X34 : $i, X36 : $i]:
% 0.77/0.96         ((r1_tarski @ X36 @ X34) | ~ (r2_hidden @ X36 @ (k1_zfmisc_1 @ X34)))),
% 0.77/0.96      inference('simplify', [status(thm)], ['28'])).
% 0.77/0.96  thf('30', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.77/0.96      inference('sup-', [status(thm)], ['27', '29'])).
% 0.77/0.96  thf(t63_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.77/0.96       ( r1_xboole_0 @ A @ C ) ))).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X20 @ X21)
% 0.77/0.96          | ~ (r1_xboole_0 @ X21 @ X22)
% 0.77/0.96          | (r1_xboole_0 @ X20 @ X22))),
% 0.77/0.96      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['30', '31'])).
% 0.77/0.96  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['22', '32'])).
% 0.77/0.96  thf(d7_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.77/0.96       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (![X4 : $i, X5 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.77/0.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['33', '34'])).
% 0.77/0.96  thf(t48_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['36', '37'])).
% 0.77/0.96  thf('39', plain,
% 0.77/0.96      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.77/0.96         = (k3_xboole_0 @ sk_B @ 
% 0.77/0.96            (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['35', '38'])).
% 0.77/0.96  thf(idempotence_k3_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/0.96  thf('40', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/0.96  thf(t100_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (![X8 : $i, X9 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X8 @ X9)
% 0.77/0.96           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['40', '41'])).
% 0.77/0.96  thf(t92_xboole_1, axiom,
% 0.77/0.96    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.77/0.96  thf('43', plain, (![X32 : $i]: ((k5_xboole_0 @ X32 @ X32) = (k1_xboole_0))),
% 0.77/0.96      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/0.96  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['42', '43'])).
% 0.77/0.96  thf('45', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.96  thf('47', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/0.96  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['46', '47'])).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf(t47_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.77/0.96  thf('50', plain,
% 0.77/0.96      (![X15 : $i, X16 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.77/0.96           = (k4_xboole_0 @ X15 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.77/0.96  thf(commutativity_k3_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('52', plain,
% 0.77/0.96      (![X8 : $i, X9 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X8 @ X9)
% 0.77/0.96           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/0.96  thf('53', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X0 @ X1)
% 0.77/0.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['51', '52'])).
% 0.77/0.96  thf('54', plain, (![X32 : $i]: ((k5_xboole_0 @ X32 @ X32) = (k1_xboole_0))),
% 0.77/0.96      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/0.96  thf(t91_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.77/0.96       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.77/0.96  thf('55', plain,
% 0.77/0.96      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.77/0.96         ((k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ X31)
% 0.77/0.96           = (k5_xboole_0 @ X29 @ (k5_xboole_0 @ X30 @ X31)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/0.96           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['54', '55'])).
% 0.77/0.96  thf(commutativity_k5_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.77/0.96  thf('57', plain,
% 0.77/0.96      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/0.96  thf(t5_boole, axiom,
% 0.77/0.96    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/0.96  thf('58', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t5_boole])).
% 0.77/0.96  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['57', '58'])).
% 0.77/0.96  thf('60', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('demod', [status(thm)], ['56', '59'])).
% 0.77/0.96  thf('61', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X0 @ X1)
% 0.77/0.96           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['53', '60'])).
% 0.77/0.96  thf('62', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.77/0.96           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['50', '61'])).
% 0.77/0.96  thf('63', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('64', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X0 @ X1)
% 0.77/0.96           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['53', '60'])).
% 0.77/0.96  thf('65', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.77/0.96  thf('66', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('67', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.77/0.96      inference('demod', [status(thm)], ['39', '48', '49', '65', '66'])).
% 0.77/0.96  thf('68', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf(t17_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.77/0.96  thf('69', plain,
% 0.77/0.96      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 0.77/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.77/0.96  thf('70', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.77/0.96      inference('sup+', [status(thm)], ['68', '69'])).
% 0.77/0.96  thf('71', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.77/0.96      inference('sup+', [status(thm)], ['67', '70'])).
% 0.77/0.96  thf('72', plain, ($false), inference('demod', [status(thm)], ['14', '71'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
