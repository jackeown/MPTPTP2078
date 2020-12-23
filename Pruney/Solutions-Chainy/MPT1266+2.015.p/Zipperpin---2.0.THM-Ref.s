%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CGDe2Y7I3u

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:14 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  199 (1015 expanded)
%              Number of leaves         :   34 ( 315 expanded)
%              Depth                    :   27
%              Number of atoms          : 1649 (9201 expanded)
%              Number of equality atoms :  117 ( 620 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t84_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( ( k1_tops_1 @ A @ B )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tops_1])).

thf('0',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('22',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('24',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','22','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('31',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('33',plain,(
    r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_tops_1 @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = ( k2_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('41',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('42',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('53',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['3','53'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('56',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('57',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('60',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('67',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','65','66'])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['2','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('79',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['72','77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('86',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('87',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('89',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','89'])).

thf('91',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['79','90'])).

thf('92',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('94',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('99',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('100',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('101',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('102',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_pre_topc @ X24 @ X23 )
       != ( k2_struct_0 @ X24 ) )
      | ( v1_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('108',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('109',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('111',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('115',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) )
        = ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['109','116'])).

thf('118',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','89'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('120',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('121',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','89'])).

thf('123',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('125',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('127',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('130',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('132',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('135',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('136',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['133','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('139',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('141',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('143',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','143'])).

thf('145',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','144'])).

thf('146',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','145','146','147'])).

thf('149',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','148'])).

thf('150',plain,
    ( ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','149'])).

thf('151',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('152',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ X26 )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('156',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('159',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','159'])).

thf('161',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','97','98','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CGDe2Y7I3u
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.37/1.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.37/1.60  % Solved by: fo/fo7.sh
% 1.37/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.60  % done 4265 iterations in 1.146s
% 1.37/1.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.37/1.60  % SZS output start Refutation
% 1.37/1.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.37/1.60  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.37/1.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.60  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.37/1.60  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.37/1.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.37/1.60  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.37/1.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.37/1.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.37/1.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.37/1.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.37/1.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.37/1.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.37/1.60  thf(t84_tops_1, conjecture,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( l1_pre_topc @ A ) =>
% 1.37/1.60       ( ![B:$i]:
% 1.37/1.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.37/1.60           ( ( v2_tops_1 @ B @ A ) <=>
% 1.37/1.60             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.37/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.60    (~( ![A:$i]:
% 1.37/1.60        ( ( l1_pre_topc @ A ) =>
% 1.37/1.60          ( ![B:$i]:
% 1.37/1.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.37/1.60              ( ( v2_tops_1 @ B @ A ) <=>
% 1.37/1.60                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.37/1.60    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 1.37/1.60  thf('0', plain,
% 1.37/1.60      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 1.37/1.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('1', plain,
% 1.37/1.60      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.37/1.60       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.37/1.60      inference('split', [status(esa)], ['0'])).
% 1.37/1.60  thf(d3_struct_0, axiom,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.37/1.60  thf('2', plain,
% 1.37/1.60      (![X17 : $i]:
% 1.37/1.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.60  thf('3', plain,
% 1.37/1.60      (![X17 : $i]:
% 1.37/1.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.60  thf('4', plain,
% 1.37/1.60      (![X17 : $i]:
% 1.37/1.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.60  thf('5', plain,
% 1.37/1.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('6', plain,
% 1.37/1.60      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('split', [status(esa)], ['5'])).
% 1.37/1.60  thf('7', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(d4_tops_1, axiom,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( l1_pre_topc @ A ) =>
% 1.37/1.60       ( ![B:$i]:
% 1.37/1.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.37/1.60           ( ( v2_tops_1 @ B @ A ) <=>
% 1.37/1.60             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.37/1.60  thf('8', plain,
% 1.37/1.60      (![X25 : $i, X26 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.37/1.60          | ~ (v2_tops_1 @ X25 @ X26)
% 1.37/1.60          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25) @ X26)
% 1.37/1.60          | ~ (l1_pre_topc @ X26))),
% 1.37/1.60      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.37/1.60  thf('9', plain,
% 1.37/1.60      ((~ (l1_pre_topc @ sk_A)
% 1.37/1.60        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.37/1.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['7', '8'])).
% 1.37/1.60  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('11', plain,
% 1.37/1.60      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.37/1.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.37/1.60      inference('demod', [status(thm)], ['9', '10'])).
% 1.37/1.60  thf('12', plain,
% 1.37/1.60      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['6', '11'])).
% 1.37/1.60  thf('13', plain,
% 1.37/1.60      ((((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.37/1.60         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup+', [status(thm)], ['4', '12'])).
% 1.37/1.60  thf('14', plain,
% 1.37/1.60      (![X17 : $i]:
% 1.37/1.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.60  thf('15', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('16', plain,
% 1.37/1.60      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.37/1.60        | ~ (l1_struct_0 @ sk_A))),
% 1.37/1.60      inference('sup+', [status(thm)], ['14', '15'])).
% 1.37/1.60  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(dt_l1_pre_topc, axiom,
% 1.37/1.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.37/1.60  thf('18', plain,
% 1.37/1.60      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.37/1.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.37/1.60  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.37/1.60  thf('20', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['16', '19'])).
% 1.37/1.60  thf(d5_subset_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.37/1.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.37/1.60  thf('21', plain,
% 1.37/1.60      (![X8 : $i, X9 : $i]:
% 1.37/1.60         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.37/1.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.60  thf('22', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.37/1.60  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.37/1.60  thf('24', plain,
% 1.37/1.60      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['13', '22', '23'])).
% 1.37/1.60  thf('25', plain,
% 1.37/1.60      (![X17 : $i]:
% 1.37/1.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.60  thf('26', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('27', plain,
% 1.37/1.60      (![X8 : $i, X9 : $i]:
% 1.37/1.60         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.37/1.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.60  thf('28', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['26', '27'])).
% 1.37/1.60  thf('29', plain,
% 1.37/1.60      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.37/1.60        | ~ (l1_struct_0 @ sk_A))),
% 1.37/1.60      inference('sup+', [status(thm)], ['25', '28'])).
% 1.37/1.60  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.37/1.60  thf('31', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['29', '30'])).
% 1.37/1.60  thf(t36_xboole_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.37/1.60  thf('32', plain,
% 1.37/1.60      (![X1 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ X1)),
% 1.37/1.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.37/1.60  thf('33', plain,
% 1.37/1.60      ((r1_tarski @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.37/1.60        (u1_struct_0 @ sk_A))),
% 1.37/1.60      inference('sup+', [status(thm)], ['31', '32'])).
% 1.37/1.60  thf(t3_subset, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.37/1.60  thf('34', plain,
% 1.37/1.60      (![X14 : $i, X16 : $i]:
% 1.37/1.60         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 1.37/1.60      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.60  thf('35', plain,
% 1.37/1.60      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.60  thf(d3_tops_1, axiom,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( l1_pre_topc @ A ) =>
% 1.37/1.60       ( ![B:$i]:
% 1.37/1.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.37/1.60           ( ( v1_tops_1 @ B @ A ) <=>
% 1.37/1.60             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 1.37/1.60  thf('36', plain,
% 1.37/1.60      (![X23 : $i, X24 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.37/1.60          | ~ (v1_tops_1 @ X23 @ X24)
% 1.37/1.60          | ((k2_pre_topc @ X24 @ X23) = (k2_struct_0 @ X24))
% 1.37/1.60          | ~ (l1_pre_topc @ X24))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.37/1.60  thf('37', plain,
% 1.37/1.60      ((~ (l1_pre_topc @ sk_A)
% 1.37/1.60        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.37/1.60            = (k2_struct_0 @ sk_A))
% 1.37/1.60        | ~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['35', '36'])).
% 1.37/1.60  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('39', plain,
% 1.37/1.60      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.37/1.60          = (k2_struct_0 @ sk_A))
% 1.37/1.60        | ~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.37/1.60      inference('demod', [status(thm)], ['37', '38'])).
% 1.37/1.60  thf('40', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.37/1.60  thf('41', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.37/1.60  thf('42', plain,
% 1.37/1.60      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.37/1.60          = (k2_struct_0 @ sk_A))
% 1.37/1.60        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.37/1.60      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.37/1.60  thf('43', plain,
% 1.37/1.60      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.37/1.60          = (k2_struct_0 @ sk_A)))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['24', '42'])).
% 1.37/1.60  thf('44', plain,
% 1.37/1.60      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.60  thf(dt_k2_pre_topc, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( ( l1_pre_topc @ A ) & 
% 1.37/1.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.37/1.60       ( m1_subset_1 @
% 1.37/1.60         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.37/1.60  thf('45', plain,
% 1.37/1.60      (![X18 : $i, X19 : $i]:
% 1.37/1.60         (~ (l1_pre_topc @ X18)
% 1.37/1.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.37/1.60          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 1.37/1.60             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.37/1.60      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.37/1.60  thf('46', plain,
% 1.37/1.60      (((m1_subset_1 @ 
% 1.37/1.60         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.37/1.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.37/1.60        | ~ (l1_pre_topc @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['44', '45'])).
% 1.37/1.60  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('48', plain,
% 1.37/1.60      ((m1_subset_1 @ 
% 1.37/1.60        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['46', '47'])).
% 1.37/1.60  thf('49', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.37/1.60  thf('50', plain,
% 1.37/1.60      ((m1_subset_1 @ 
% 1.37/1.60        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['48', '49'])).
% 1.37/1.60  thf('51', plain,
% 1.37/1.60      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.37/1.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup+', [status(thm)], ['43', '50'])).
% 1.37/1.60  thf('52', plain,
% 1.37/1.60      (![X8 : $i, X9 : $i]:
% 1.37/1.60         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.37/1.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.60  thf('53', plain,
% 1.37/1.60      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.37/1.60          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['51', '52'])).
% 1.37/1.60  thf('54', plain,
% 1.37/1.60      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.37/1.60           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.37/1.60         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup+', [status(thm)], ['3', '53'])).
% 1.37/1.60  thf(dt_k2_subset_1, axiom,
% 1.37/1.60    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.37/1.60  thf('55', plain,
% 1.37/1.60      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 1.37/1.60      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.37/1.60  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.37/1.60  thf('56', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 1.37/1.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.37/1.60  thf('57', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 1.37/1.60      inference('demod', [status(thm)], ['55', '56'])).
% 1.37/1.60  thf('58', plain,
% 1.37/1.60      (![X8 : $i, X9 : $i]:
% 1.37/1.60         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.37/1.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.60  thf('59', plain,
% 1.37/1.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['57', '58'])).
% 1.37/1.60  thf(t3_boole, axiom,
% 1.37/1.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.37/1.60  thf('60', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 1.37/1.60      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.60  thf(t48_xboole_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.37/1.60  thf('61', plain,
% 1.37/1.60      (![X4 : $i, X5 : $i]:
% 1.37/1.60         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 1.37/1.60           = (k3_xboole_0 @ X4 @ X5))),
% 1.37/1.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.37/1.60  thf('62', plain,
% 1.37/1.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['60', '61'])).
% 1.37/1.60  thf(t2_boole, axiom,
% 1.37/1.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.37/1.60  thf('63', plain,
% 1.37/1.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [t2_boole])).
% 1.37/1.60  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.60      inference('demod', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('65', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.60      inference('demod', [status(thm)], ['59', '64'])).
% 1.37/1.60  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.37/1.60  thf('67', plain,
% 1.37/1.60      ((((k1_xboole_0)
% 1.37/1.60          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['54', '65', '66'])).
% 1.37/1.60  thf('68', plain,
% 1.37/1.60      (![X4 : $i, X5 : $i]:
% 1.37/1.60         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 1.37/1.60           = (k3_xboole_0 @ X4 @ X5))),
% 1.37/1.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.37/1.60  thf('69', plain,
% 1.37/1.60      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.37/1.60          = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup+', [status(thm)], ['67', '68'])).
% 1.37/1.60  thf('70', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 1.37/1.60      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.60  thf('71', plain,
% 1.37/1.60      ((((u1_struct_0 @ sk_A)
% 1.37/1.60          = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['69', '70'])).
% 1.37/1.60  thf('72', plain,
% 1.37/1.60      (((((u1_struct_0 @ sk_A)
% 1.37/1.60           = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.37/1.60         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup+', [status(thm)], ['2', '71'])).
% 1.37/1.60  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.60      inference('demod', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('74', plain,
% 1.37/1.60      (![X4 : $i, X5 : $i]:
% 1.37/1.60         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 1.37/1.60           = (k3_xboole_0 @ X4 @ X5))),
% 1.37/1.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.37/1.60  thf('75', plain,
% 1.37/1.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['73', '74'])).
% 1.37/1.60  thf('76', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 1.37/1.60      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.60  thf('77', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['75', '76'])).
% 1.37/1.60  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.37/1.60  thf('79', plain,
% 1.37/1.60      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['72', '77', '78'])).
% 1.37/1.60  thf('80', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(d1_tops_1, axiom,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( l1_pre_topc @ A ) =>
% 1.37/1.60       ( ![B:$i]:
% 1.37/1.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.37/1.60           ( ( k1_tops_1 @ A @ B ) =
% 1.37/1.60             ( k3_subset_1 @
% 1.37/1.60               ( u1_struct_0 @ A ) @ 
% 1.37/1.60               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.37/1.60  thf('81', plain,
% 1.37/1.60      (![X21 : $i, X22 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.37/1.60          | ((k1_tops_1 @ X22 @ X21)
% 1.37/1.60              = (k3_subset_1 @ (u1_struct_0 @ X22) @ 
% 1.37/1.60                 (k2_pre_topc @ X22 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21))))
% 1.37/1.60          | ~ (l1_pre_topc @ X22))),
% 1.37/1.60      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.37/1.60  thf('82', plain,
% 1.37/1.60      ((~ (l1_pre_topc @ sk_A)
% 1.37/1.60        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.37/1.60            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60               (k2_pre_topc @ sk_A @ 
% 1.37/1.60                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['80', '81'])).
% 1.37/1.60  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('84', plain,
% 1.37/1.60      (((k1_tops_1 @ sk_A @ sk_B)
% 1.37/1.60         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.37/1.60      inference('demod', [status(thm)], ['82', '83'])).
% 1.37/1.60  thf('85', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['26', '27'])).
% 1.37/1.60  thf('86', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['29', '30'])).
% 1.37/1.60  thf('87', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['85', '86'])).
% 1.37/1.60  thf('88', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.37/1.60  thf('89', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['87', '88'])).
% 1.37/1.60  thf('90', plain,
% 1.37/1.60      (((k1_tops_1 @ sk_A @ sk_B)
% 1.37/1.60         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.37/1.60      inference('demod', [status(thm)], ['84', '89'])).
% 1.37/1.60  thf('91', plain,
% 1.37/1.60      ((((k1_tops_1 @ sk_A @ sk_B)
% 1.37/1.60          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.37/1.60             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup+', [status(thm)], ['79', '90'])).
% 1.37/1.60  thf('92', plain,
% 1.37/1.60      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.37/1.60          = (k2_struct_0 @ sk_A)))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['24', '42'])).
% 1.37/1.60  thf('93', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.60      inference('demod', [status(thm)], ['59', '64'])).
% 1.37/1.60  thf('94', plain,
% 1.37/1.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.37/1.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.37/1.60  thf('95', plain,
% 1.37/1.60      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 1.37/1.60         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.37/1.60      inference('split', [status(esa)], ['0'])).
% 1.37/1.60  thf('96', plain,
% 1.37/1.60      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.37/1.60         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 1.37/1.60             ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['94', '95'])).
% 1.37/1.60  thf('97', plain,
% 1.37/1.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.37/1.60       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.37/1.60      inference('simplify', [status(thm)], ['96'])).
% 1.37/1.60  thf('98', plain,
% 1.37/1.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.37/1.60       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.37/1.60      inference('split', [status(esa)], ['5'])).
% 1.37/1.60  thf('99', plain,
% 1.37/1.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.37/1.60         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.37/1.60      inference('split', [status(esa)], ['5'])).
% 1.37/1.60  thf('100', plain,
% 1.37/1.60      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.60  thf('101', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.37/1.60  thf('102', plain,
% 1.37/1.60      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['100', '101'])).
% 1.37/1.60  thf('103', plain,
% 1.37/1.60      (![X23 : $i, X24 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.37/1.60          | ((k2_pre_topc @ X24 @ X23) != (k2_struct_0 @ X24))
% 1.37/1.60          | (v1_tops_1 @ X23 @ X24)
% 1.37/1.60          | ~ (l1_pre_topc @ X24))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.37/1.60  thf('104', plain,
% 1.37/1.60      ((~ (l1_pre_topc @ sk_A)
% 1.37/1.60        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.37/1.60        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.37/1.60            != (k2_struct_0 @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['102', '103'])).
% 1.37/1.60  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('106', plain,
% 1.37/1.60      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.37/1.60        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.37/1.60            != (k2_struct_0 @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['104', '105'])).
% 1.37/1.60  thf('107', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['29', '30'])).
% 1.37/1.60  thf('108', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.37/1.60  thf('109', plain,
% 1.37/1.60      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['107', '108'])).
% 1.37/1.60  thf('110', plain,
% 1.37/1.60      (![X1 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ X1)),
% 1.37/1.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.37/1.60  thf('111', plain,
% 1.37/1.60      (![X14 : $i, X16 : $i]:
% 1.37/1.60         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 1.37/1.60      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.60  thf('112', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['110', '111'])).
% 1.37/1.60  thf('113', plain,
% 1.37/1.60      (![X18 : $i, X19 : $i]:
% 1.37/1.60         (~ (l1_pre_topc @ X18)
% 1.37/1.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.37/1.60          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 1.37/1.60             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.37/1.60      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.37/1.60  thf('114', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         ((m1_subset_1 @ 
% 1.37/1.60           (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 1.37/1.60           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.37/1.60          | ~ (l1_pre_topc @ X0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['112', '113'])).
% 1.37/1.60  thf(involutiveness_k3_subset_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.37/1.60       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.37/1.60  thf('115', plain,
% 1.37/1.60      (![X11 : $i, X12 : $i]:
% 1.37/1.60         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 1.37/1.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.37/1.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.37/1.60  thf('116', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (~ (l1_pre_topc @ X0)
% 1.37/1.60          | ((k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.37/1.60              (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.37/1.60               (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))
% 1.37/1.60              = (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['114', '115'])).
% 1.37/1.60  thf('117', plain,
% 1.37/1.60      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.37/1.60          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.37/1.60        | ~ (l1_pre_topc @ sk_A))),
% 1.37/1.60      inference('sup+', [status(thm)], ['109', '116'])).
% 1.37/1.60  thf('118', plain,
% 1.37/1.60      (((k1_tops_1 @ sk_A @ sk_B)
% 1.37/1.60         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.37/1.60      inference('demod', [status(thm)], ['84', '89'])).
% 1.37/1.60  thf('119', plain,
% 1.37/1.60      ((m1_subset_1 @ 
% 1.37/1.60        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['48', '49'])).
% 1.37/1.60  thf('120', plain,
% 1.37/1.60      (![X8 : $i, X9 : $i]:
% 1.37/1.60         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.37/1.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.60  thf('121', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['119', '120'])).
% 1.37/1.60  thf('122', plain,
% 1.37/1.60      (((k1_tops_1 @ sk_A @ sk_B)
% 1.37/1.60         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.37/1.60      inference('demod', [status(thm)], ['84', '89'])).
% 1.37/1.60  thf('123', plain,
% 1.37/1.60      (((k1_tops_1 @ sk_A @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.37/1.60      inference('sup+', [status(thm)], ['121', '122'])).
% 1.37/1.60  thf('124', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['110', '111'])).
% 1.37/1.60  thf('125', plain,
% 1.37/1.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('sup+', [status(thm)], ['123', '124'])).
% 1.37/1.60  thf('126', plain,
% 1.37/1.60      (![X8 : $i, X9 : $i]:
% 1.37/1.60         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.37/1.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.60  thf('127', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['125', '126'])).
% 1.37/1.60  thf('128', plain,
% 1.37/1.60      (![X17 : $i]:
% 1.37/1.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.60  thf('129', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['125', '126'])).
% 1.37/1.60  thf('130', plain,
% 1.37/1.60      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.37/1.60        | ~ (l1_struct_0 @ sk_A))),
% 1.37/1.60      inference('sup+', [status(thm)], ['128', '129'])).
% 1.37/1.60  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.37/1.60  thf('132', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.37/1.60      inference('demod', [status(thm)], ['130', '131'])).
% 1.37/1.60  thf('133', plain,
% 1.37/1.60      (![X17 : $i]:
% 1.37/1.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.60  thf('134', plain,
% 1.37/1.60      (((k1_tops_1 @ sk_A @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.60            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.37/1.60      inference('sup+', [status(thm)], ['121', '122'])).
% 1.37/1.60  thf('135', plain,
% 1.37/1.60      (![X1 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ X1)),
% 1.37/1.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.37/1.60  thf('136', plain,
% 1.37/1.60      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.37/1.60      inference('sup+', [status(thm)], ['134', '135'])).
% 1.37/1.60  thf('137', plain,
% 1.37/1.60      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_struct_0 @ sk_A))
% 1.37/1.60        | ~ (l1_struct_0 @ sk_A))),
% 1.37/1.60      inference('sup+', [status(thm)], ['133', '136'])).
% 1.37/1.60  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.37/1.60  thf('139', plain,
% 1.37/1.60      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_struct_0 @ sk_A))),
% 1.37/1.60      inference('demod', [status(thm)], ['137', '138'])).
% 1.37/1.60  thf('140', plain,
% 1.37/1.60      (![X14 : $i, X16 : $i]:
% 1.37/1.60         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 1.37/1.60      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.60  thf('141', plain,
% 1.37/1.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.37/1.60        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['139', '140'])).
% 1.37/1.60  thf('142', plain,
% 1.37/1.60      (![X8 : $i, X9 : $i]:
% 1.37/1.60         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 1.37/1.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.60  thf('143', plain,
% 1.37/1.60      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['141', '142'])).
% 1.37/1.60  thf('144', plain,
% 1.37/1.60      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.37/1.60      inference('demod', [status(thm)], ['132', '143'])).
% 1.37/1.60  thf('145', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.37/1.60      inference('demod', [status(thm)], ['127', '144'])).
% 1.37/1.60  thf('146', plain,
% 1.37/1.60      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['107', '108'])).
% 1.37/1.60  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('148', plain,
% 1.37/1.60      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.37/1.60      inference('demod', [status(thm)], ['117', '118', '145', '146', '147'])).
% 1.37/1.60  thf('149', plain,
% 1.37/1.60      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.37/1.60        | ((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.37/1.60            != (k2_struct_0 @ sk_A)))),
% 1.37/1.60      inference('demod', [status(thm)], ['106', '148'])).
% 1.37/1.60  thf('150', plain,
% 1.37/1.60      (((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 1.37/1.60           != (k2_struct_0 @ sk_A))
% 1.37/1.60         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 1.37/1.60         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['99', '149'])).
% 1.37/1.60  thf('151', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 1.37/1.60      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.60  thf('152', plain,
% 1.37/1.60      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 1.37/1.60         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 1.37/1.60         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.37/1.60      inference('demod', [status(thm)], ['150', '151'])).
% 1.37/1.60  thf('153', plain,
% 1.37/1.60      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.37/1.60         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.37/1.60      inference('simplify', [status(thm)], ['152'])).
% 1.37/1.60  thf('154', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('155', plain,
% 1.37/1.60      (![X25 : $i, X26 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.37/1.60          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25) @ X26)
% 1.37/1.60          | (v2_tops_1 @ X25 @ X26)
% 1.37/1.60          | ~ (l1_pre_topc @ X26))),
% 1.37/1.60      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.37/1.60  thf('156', plain,
% 1.37/1.60      ((~ (l1_pre_topc @ sk_A)
% 1.37/1.60        | (v2_tops_1 @ sk_B @ sk_A)
% 1.37/1.60        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['154', '155'])).
% 1.37/1.60  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('158', plain,
% 1.37/1.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.37/1.60         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['87', '88'])).
% 1.37/1.60  thf('159', plain,
% 1.37/1.60      (((v2_tops_1 @ sk_B @ sk_A)
% 1.37/1.60        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.37/1.60      inference('demod', [status(thm)], ['156', '157', '158'])).
% 1.37/1.60  thf('160', plain,
% 1.37/1.60      (((v2_tops_1 @ sk_B @ sk_A))
% 1.37/1.60         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['153', '159'])).
% 1.37/1.60  thf('161', plain,
% 1.37/1.60      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.37/1.60      inference('split', [status(esa)], ['0'])).
% 1.37/1.60  thf('162', plain,
% 1.37/1.60      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.37/1.60       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['160', '161'])).
% 1.37/1.60  thf('163', plain, ($false),
% 1.37/1.60      inference('sat_resolution*', [status(thm)], ['1', '97', '98', '162'])).
% 1.37/1.60  
% 1.37/1.60  % SZS output end Refutation
% 1.37/1.60  
% 1.37/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
