%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6ljP4Fhmv

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:59 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 528 expanded)
%              Number of leaves         :   37 ( 183 expanded)
%              Depth                    :   15
%              Number of atoms          : 1015 (4215 expanded)
%              Number of equality atoms :   75 ( 363 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t43_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ C )
            <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X59: $i,X60: $i] :
      ( ( ( k3_subset_1 @ X59 @ X60 )
        = ( k4_xboole_0 @ X59 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('41',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','39','42'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','47'])).

thf('49',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['6','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['5','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('55',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X64 ) )
      | ( r1_tarski @ X63 @ ( k3_subset_1 @ X64 @ X65 ) )
      | ~ ( r1_tarski @ X65 @ ( k3_subset_1 @ X64 @ X63 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('64',plain,(
    ! [X62: $i] :
      ( ( k2_subset_1 @ X62 )
      = ( k3_subset_1 @ X62 @ ( k1_subset_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('65',plain,(
    ! [X58: $i] :
      ( ( k2_subset_1 @ X58 )
      = X58 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('66',plain,(
    ! [X57: $i] :
      ( ( k1_subset_1 @ X57 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('67',plain,(
    ! [X62: $i] :
      ( X62
      = ( k3_subset_1 @ X62 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('70',plain,(
    ! [X61: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X61 ) @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('71',plain,(
    ! [X57: $i] :
      ( ( k1_subset_1 @ X57 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('72',plain,(
    ! [X61: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['62','68','73'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r1_tarski @ X6 @ ( k5_xboole_0 @ X7 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X9 ) )
      | ~ ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_C @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['53','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X64 ) )
      | ( r1_tarski @ X63 @ ( k3_subset_1 @ X64 @ X65 ) )
      | ~ ( r1_tarski @ X65 @ ( k3_subset_1 @ X64 @ X63 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X59: $i,X60: $i] :
      ( ( ( k3_subset_1 @ X59 @ X60 )
        = ( k4_xboole_0 @ X59 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('90',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','67'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('95',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_A ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['83','95'])).

thf('97',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('98',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['6','50','97'])).

thf('99',plain,(
    r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['96','98'])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k5_xboole_0 @ sk_C @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['99','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['52','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6ljP4Fhmv
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:38:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.78/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/0.99  % Solved by: fo/fo7.sh
% 0.78/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.99  % done 1748 iterations in 0.523s
% 0.78/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/0.99  % SZS output start Refutation
% 0.78/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.78/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.78/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.99  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.78/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/0.99  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.78/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.78/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.78/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(t43_subset_1, conjecture,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99       ( ![C:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.78/0.99             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.78/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.99    (~( ![A:$i,B:$i]:
% 0.78/0.99        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99          ( ![C:$i]:
% 0.78/0.99            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.78/0.99                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.78/0.99    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.78/0.99  thf('0', plain,
% 0.78/0.99      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.78/0.99        | ~ (r1_xboole_0 @ sk_B @ sk_C))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('1', plain,
% 0.78/0.99      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.78/0.99         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.78/0.99      inference('split', [status(esa)], ['0'])).
% 0.78/0.99  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(d5_subset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.78/0.99  thf('3', plain,
% 0.78/0.99      (![X59 : $i, X60 : $i]:
% 0.78/0.99         (((k3_subset_1 @ X59 @ X60) = (k4_xboole_0 @ X59 @ X60))
% 0.78/0.99          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.78/0.99      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/0.99  thf('4', plain,
% 0.78/0.99      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('5', plain,
% 0.78/0.99      ((~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.78/0.99         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.78/0.99      inference('demod', [status(thm)], ['1', '4'])).
% 0.78/0.99  thf('6', plain,
% 0.78/0.99      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.78/0.99       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.78/0.99      inference('split', [status(esa)], ['0'])).
% 0.78/0.99  thf('7', plain,
% 0.78/0.99      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('8', plain,
% 0.78/0.99      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.78/0.99        | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('9', plain,
% 0.78/0.99      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.78/0.99         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.78/0.99      inference('split', [status(esa)], ['8'])).
% 0.78/0.99  thf('10', plain,
% 0.78/0.99      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.78/0.99         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '9'])).
% 0.78/0.99  thf(t95_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( k3_xboole_0 @ A @ B ) =
% 0.78/0.99       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.78/0.99  thf('11', plain,
% 0.78/0.99      (![X24 : $i, X25 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X24 @ X25)
% 0.78/0.99           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.78/0.99              (k2_xboole_0 @ X24 @ X25)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.78/0.99  thf(t91_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.78/0.99       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.78/0.99  thf('12', plain,
% 0.78/0.99      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.78/0.99           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.99  thf('13', plain,
% 0.78/0.99      (![X24 : $i, X25 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X24 @ X25)
% 0.78/0.99           = (k5_xboole_0 @ X24 @ 
% 0.78/0.99              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.78/0.99      inference('demod', [status(thm)], ['11', '12'])).
% 0.78/0.99  thf(t92_xboole_1, axiom,
% 0.78/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.78/0.99  thf('14', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.99  thf('15', plain,
% 0.78/0.99      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.78/0.99           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.99  thf('16', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.78/0.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['14', '15'])).
% 0.78/0.99  thf('17', plain,
% 0.78/0.99      (![X24 : $i, X25 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X24 @ X25)
% 0.78/0.99           = (k5_xboole_0 @ X24 @ 
% 0.78/0.99              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.78/0.99      inference('demod', [status(thm)], ['11', '12'])).
% 0.78/0.99  thf('18', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.78/0.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['14', '15'])).
% 0.78/0.99  thf('19', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.78/0.99           = (k3_xboole_0 @ X0 @ X0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['17', '18'])).
% 0.78/0.99  thf(idempotence_k2_xboole_0, axiom,
% 0.78/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/0.99  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.78/0.99      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.78/0.99  thf(idempotence_k3_xboole_0, axiom,
% 0.78/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/0.99  thf('21', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.78/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.99  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.78/0.99      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.78/0.99  thf('23', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.99      inference('demod', [status(thm)], ['16', '22'])).
% 0.78/0.99  thf('24', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.78/0.99           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['13', '23'])).
% 0.78/0.99  thf(t100_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/0.99  thf('25', plain,
% 0.78/0.99      (![X4 : $i, X5 : $i]:
% 0.78/0.99         ((k4_xboole_0 @ X4 @ X5)
% 0.78/0.99           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.99  thf('26', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.78/0.99           = (k4_xboole_0 @ X1 @ X0))),
% 0.78/0.99      inference('demod', [status(thm)], ['24', '25'])).
% 0.78/0.99  thf(t107_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.78/0.99       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.78/0.99         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.78/0.99  thf('27', plain,
% 0.78/0.99      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.78/0.99         ((r1_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 0.78/0.99          | ~ (r1_tarski @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.78/0.99  thf('28', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.99         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.78/0.99          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['26', '27'])).
% 0.78/0.99  thf(commutativity_k2_tarski, axiom,
% 0.78/0.99    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.78/0.99  thf('29', plain,
% 0.78/0.99      (![X26 : $i, X27 : $i]:
% 0.78/0.99         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 0.78/0.99      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.78/0.99  thf(l51_zfmisc_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.99  thf('30', plain,
% 0.78/0.99      (![X55 : $i, X56 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.78/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.99  thf('31', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.78/0.99      inference('sup+', [status(thm)], ['29', '30'])).
% 0.78/0.99  thf('32', plain,
% 0.78/0.99      (![X55 : $i, X56 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.78/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.99  thf('33', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.78/0.99      inference('sup+', [status(thm)], ['31', '32'])).
% 0.78/0.99  thf(t6_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.99  thf('34', plain,
% 0.78/0.99      (![X14 : $i, X15 : $i]:
% 0.78/0.99         ((k2_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15))
% 0.78/0.99           = (k2_xboole_0 @ X14 @ X15))),
% 0.78/0.99      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.78/0.99  thf('35', plain,
% 0.78/0.99      (![X24 : $i, X25 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X24 @ X25)
% 0.78/0.99           = (k5_xboole_0 @ X24 @ 
% 0.78/0.99              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.78/0.99      inference('demod', [status(thm)], ['11', '12'])).
% 0.78/0.99  thf('36', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.78/0.99           = (k5_xboole_0 @ X1 @ 
% 0.78/0.99              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 0.78/0.99      inference('sup+', [status(thm)], ['34', '35'])).
% 0.78/0.99  thf('37', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.78/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.99  thf('38', plain,
% 0.78/0.99      (![X4 : $i, X5 : $i]:
% 0.78/0.99         ((k4_xboole_0 @ X4 @ X5)
% 0.78/0.99           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.99  thf('39', plain,
% 0.78/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['37', '38'])).
% 0.78/0.99  thf('40', plain,
% 0.78/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['37', '38'])).
% 0.78/0.99  thf('41', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.99  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['40', '41'])).
% 0.78/0.99  thf('43', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.78/0.99           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.78/0.99      inference('demod', [status(thm)], ['36', '39', '42'])).
% 0.78/0.99  thf(t5_boole, axiom,
% 0.78/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.78/0.99  thf('44', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.78/0.99      inference('cnf', [status(esa)], [t5_boole])).
% 0.78/0.99  thf('45', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.78/0.99      inference('demod', [status(thm)], ['43', '44'])).
% 0.78/0.99  thf('46', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['33', '45'])).
% 0.78/0.99  thf('47', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.99         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.78/0.99          | (r1_xboole_0 @ X2 @ X0))),
% 0.78/0.99      inference('demod', [status(thm)], ['28', '46'])).
% 0.78/0.99  thf('48', plain,
% 0.78/0.99      (((r1_xboole_0 @ sk_B @ sk_C))
% 0.78/0.99         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['10', '47'])).
% 0.78/0.99  thf('49', plain,
% 0.78/0.99      ((~ (r1_xboole_0 @ sk_B @ sk_C)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.78/0.99      inference('split', [status(esa)], ['0'])).
% 0.78/0.99  thf('50', plain,
% 0.78/0.99      (((r1_xboole_0 @ sk_B @ sk_C)) | 
% 0.78/0.99       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['48', '49'])).
% 0.78/0.99  thf('51', plain, (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.78/0.99      inference('sat_resolution*', [status(thm)], ['6', '50'])).
% 0.78/0.99  thf('52', plain, (~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.99      inference('simpl_trail', [status(thm)], ['5', '51'])).
% 0.78/0.99  thf('53', plain,
% 0.78/0.99      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.78/0.99      inference('split', [status(esa)], ['8'])).
% 0.78/0.99  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['40', '41'])).
% 0.78/0.99  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.78/0.99  thf('55', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.78/0.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.78/0.99  thf('56', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.78/0.99      inference('sup+', [status(thm)], ['54', '55'])).
% 0.78/0.99  thf('57', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(t35_subset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99       ( ![C:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.78/0.99             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.78/0.99  thf('58', plain,
% 0.78/0.99      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 0.78/0.99          | (r1_tarski @ X63 @ (k3_subset_1 @ X64 @ X65))
% 0.78/0.99          | ~ (r1_tarski @ X65 @ (k3_subset_1 @ X64 @ X63))
% 0.78/0.99          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.78/0.99  thf('59', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.99          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.78/0.99          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['57', '58'])).
% 0.78/0.99  thf('60', plain,
% 0.78/0.99      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('61', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.99          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.78/0.99          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.78/0.99      inference('demod', [status(thm)], ['59', '60'])).
% 0.78/0.99  thf('62', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         ((r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ (k4_xboole_0 @ X0 @ X0)))
% 0.78/0.99          | ~ (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['56', '61'])).
% 0.78/0.99  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['40', '41'])).
% 0.78/0.99  thf(t22_subset_1, axiom,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.78/0.99  thf('64', plain,
% 0.78/0.99      (![X62 : $i]:
% 0.78/0.99         ((k2_subset_1 @ X62) = (k3_subset_1 @ X62 @ (k1_subset_1 @ X62)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.78/0.99  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.78/0.99  thf('65', plain, (![X58 : $i]: ((k2_subset_1 @ X58) = (X58))),
% 0.78/0.99      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.78/0.99  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.78/0.99  thf('66', plain, (![X57 : $i]: ((k1_subset_1 @ X57) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.78/0.99  thf('67', plain, (![X62 : $i]: ((X62) = (k3_subset_1 @ X62 @ k1_xboole_0))),
% 0.78/0.99      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.78/0.99  thf('68', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((X1) = (k3_subset_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['63', '67'])).
% 0.78/0.99  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['40', '41'])).
% 0.78/0.99  thf(dt_k1_subset_1, axiom,
% 0.78/0.99    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.78/0.99  thf('70', plain,
% 0.78/0.99      (![X61 : $i]: (m1_subset_1 @ (k1_subset_1 @ X61) @ (k1_zfmisc_1 @ X61))),
% 0.78/0.99      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.78/0.99  thf('71', plain, (![X57 : $i]: ((k1_subset_1 @ X57) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.78/0.99  thf('72', plain,
% 0.78/0.99      (![X61 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.78/0.99      inference('demod', [status(thm)], ['70', '71'])).
% 0.78/0.99  thf('73', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.78/0.99      inference('sup+', [status(thm)], ['69', '72'])).
% 0.78/0.99  thf('74', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.78/0.99      inference('demod', [status(thm)], ['62', '68', '73'])).
% 0.78/0.99  thf(t12_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.78/0.99  thf('75', plain,
% 0.78/0.99      (![X10 : $i, X11 : $i]:
% 0.78/0.99         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.78/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.78/0.99  thf('76', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 0.78/0.99      inference('sup-', [status(thm)], ['74', '75'])).
% 0.78/0.99  thf('77', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.78/0.99      inference('demod', [status(thm)], ['43', '44'])).
% 0.78/0.99  thf('78', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.78/0.99      inference('sup+', [status(thm)], ['76', '77'])).
% 0.78/0.99  thf('79', plain,
% 0.78/0.99      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.78/0.99         ((r1_tarski @ X6 @ (k5_xboole_0 @ X7 @ X9))
% 0.78/0.99          | ~ (r1_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X9))
% 0.78/0.99          | ~ (r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X9)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.78/0.99  thf('80', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.78/0.99          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_C @ sk_A))
% 0.78/0.99          | (r1_tarski @ X0 @ (k5_xboole_0 @ sk_C @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['78', '79'])).
% 0.78/0.99  thf('81', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 0.78/0.99      inference('sup-', [status(thm)], ['74', '75'])).
% 0.78/0.99  thf('82', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.78/0.99          | ~ (r1_tarski @ X0 @ sk_A)
% 0.78/0.99          | (r1_tarski @ X0 @ (k5_xboole_0 @ sk_C @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['80', '81'])).
% 0.78/0.99  thf('83', plain,
% 0.78/0.99      ((((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_C @ sk_A))
% 0.78/0.99         | ~ (r1_tarski @ sk_B @ sk_A))) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['53', '82'])).
% 0.78/0.99  thf('84', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.78/0.99      inference('sup+', [status(thm)], ['54', '55'])).
% 0.78/0.99  thf('85', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('86', plain,
% 0.78/0.99      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 0.78/0.99          | (r1_tarski @ X63 @ (k3_subset_1 @ X64 @ X65))
% 0.78/0.99          | ~ (r1_tarski @ X65 @ (k3_subset_1 @ X64 @ X63))
% 0.78/0.99          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.78/0.99  thf('87', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.99          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.78/0.99          | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ X0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['85', '86'])).
% 0.78/0.99  thf('88', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('89', plain,
% 0.78/0.99      (![X59 : $i, X60 : $i]:
% 0.78/0.99         (((k3_subset_1 @ X59 @ X60) = (k4_xboole_0 @ X59 @ X60))
% 0.78/0.99          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.78/0.99      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/0.99  thf('90', plain,
% 0.78/0.99      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.99      inference('sup-', [status(thm)], ['88', '89'])).
% 0.78/0.99  thf('91', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.99          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.78/0.99          | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ X0)))),
% 0.78/0.99      inference('demod', [status(thm)], ['87', '90'])).
% 0.78/0.99  thf('92', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ (k4_xboole_0 @ X0 @ X0)))
% 0.78/0.99          | ~ (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['84', '91'])).
% 0.78/0.99  thf('93', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((X1) = (k3_subset_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['63', '67'])).
% 0.78/0.99  thf('94', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.78/0.99      inference('sup+', [status(thm)], ['69', '72'])).
% 0.78/0.99  thf('95', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.78/0.99      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.78/0.99  thf('96', plain,
% 0.78/0.99      (((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_C @ sk_A)))
% 0.78/0.99         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['83', '95'])).
% 0.78/0.99  thf('97', plain,
% 0.78/0.99      (((r1_xboole_0 @ sk_B @ sk_C)) | 
% 0.78/0.99       ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.78/0.99      inference('split', [status(esa)], ['8'])).
% 0.78/0.99  thf('98', plain, (((r1_xboole_0 @ sk_B @ sk_C))),
% 0.78/0.99      inference('sat_resolution*', [status(thm)], ['6', '50', '97'])).
% 0.78/0.99  thf('99', plain, ((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_C @ sk_A))),
% 0.78/0.99      inference('simpl_trail', [status(thm)], ['96', '98'])).
% 0.78/0.99  thf('100', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 0.78/0.99      inference('sup-', [status(thm)], ['74', '75'])).
% 0.78/0.99  thf('101', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.78/0.99      inference('sup+', [status(thm)], ['31', '32'])).
% 0.78/0.99  thf('102', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.78/0.99           = (k4_xboole_0 @ X1 @ X0))),
% 0.78/0.99      inference('demod', [status(thm)], ['24', '25'])).
% 0.78/0.99  thf('103', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.78/0.99           = (k4_xboole_0 @ X0 @ X1))),
% 0.78/0.99      inference('sup+', [status(thm)], ['101', '102'])).
% 0.78/0.99  thf('104', plain,
% 0.78/0.99      (((k5_xboole_0 @ sk_C @ sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.99      inference('sup+', [status(thm)], ['100', '103'])).
% 0.78/0.99  thf('105', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['99', '104'])).
% 0.78/0.99  thf('106', plain, ($false), inference('demod', [status(thm)], ['52', '105'])).
% 0.78/0.99  
% 0.78/0.99  % SZS output end Refutation
% 0.78/0.99  
% 0.78/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
