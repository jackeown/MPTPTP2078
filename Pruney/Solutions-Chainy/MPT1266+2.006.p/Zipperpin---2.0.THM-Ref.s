%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.01Bu3ACXjD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:12 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  248 (2629 expanded)
%              Number of leaves         :   39 ( 839 expanded)
%              Depth                    :   25
%              Number of atoms          : 1984 (21063 expanded)
%              Number of equality atoms :  161 (1684 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('8',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tops_1 @ X28 @ X29 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','40'])).

thf('42',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v1_tops_1 @ X26 @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = ( k2_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('62',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('63',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('73',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('85',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('90',plain,(
    ! [X10: $i] :
      ( ( k1_subset_1 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('91',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = ( k3_subset_1 @ X16 @ ( k1_subset_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('92',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('93',plain,(
    ! [X16: $i] :
      ( X16
      = ( k3_subset_1 @ X16 @ ( k1_subset_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','95'])).

thf('97',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','95'])).

thf('100',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('109',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('117',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','106','115','116'])).

thf('118',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['70','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('120',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('122',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('126',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('128',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['120','128'])).

thf('130',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','105'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('133',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('135',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('138',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('139',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('140',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('141',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('143',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('144',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('146',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('149',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['147','154'])).

thf('156',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','144','155'])).

thf('157',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('158',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('159',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','159'])).

thf('161',plain,
    ( ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['138','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('163',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('165',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('166',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('167',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('168',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('169',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['166','169'])).

thf('171',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('172',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['165','172'])).

thf('174',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('175',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('177',plain,
    ( ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['164','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('180',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('181',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['163','181'])).

thf('183',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('184',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('185',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_pre_topc @ X27 @ X26 )
       != ( k2_struct_0 @ X27 ) )
      | ( v1_tops_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('187',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('191',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('192',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['182','192'])).

thf('194',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ( v2_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('197',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('201',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('203',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['194','203'])).

thf('205',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('206',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','136','137','206'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.01Bu3ACXjD
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:18:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.21/1.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.21/1.37  % Solved by: fo/fo7.sh
% 1.21/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.37  % done 3176 iterations in 0.909s
% 1.21/1.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.21/1.37  % SZS output start Refutation
% 1.21/1.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.21/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.37  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.21/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.37  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.21/1.37  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.21/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.21/1.37  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.21/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.21/1.37  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.21/1.37  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.21/1.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.21/1.37  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.21/1.37  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.21/1.37  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.21/1.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.21/1.37  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.21/1.37  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.21/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.37  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.21/1.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.37  thf(t84_tops_1, conjecture,
% 1.21/1.37    (![A:$i]:
% 1.21/1.37     ( ( l1_pre_topc @ A ) =>
% 1.21/1.37       ( ![B:$i]:
% 1.21/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.37           ( ( v2_tops_1 @ B @ A ) <=>
% 1.21/1.37             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.21/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.37    (~( ![A:$i]:
% 1.21/1.37        ( ( l1_pre_topc @ A ) =>
% 1.21/1.37          ( ![B:$i]:
% 1.21/1.37            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.37              ( ( v2_tops_1 @ B @ A ) <=>
% 1.21/1.37                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.21/1.37    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 1.21/1.37  thf('0', plain,
% 1.21/1.37      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 1.21/1.37        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('1', plain,
% 1.21/1.37      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.21/1.37       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.21/1.37      inference('split', [status(esa)], ['0'])).
% 1.21/1.37  thf(d3_struct_0, axiom,
% 1.21/1.37    (![A:$i]:
% 1.21/1.37     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.21/1.37  thf('2', plain,
% 1.21/1.37      (![X20 : $i]:
% 1.21/1.37         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.21/1.37  thf('3', plain,
% 1.21/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf(t3_subset, axiom,
% 1.21/1.37    (![A:$i,B:$i]:
% 1.21/1.37     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.21/1.37  thf('4', plain,
% 1.21/1.37      (![X17 : $i, X18 : $i]:
% 1.21/1.37         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.21/1.37      inference('cnf', [status(esa)], [t3_subset])).
% 1.21/1.37  thf('5', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.21/1.37      inference('sup-', [status(thm)], ['3', '4'])).
% 1.21/1.37  thf('6', plain,
% 1.21/1.37      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.21/1.37      inference('sup+', [status(thm)], ['2', '5'])).
% 1.21/1.37  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf(dt_l1_pre_topc, axiom,
% 1.21/1.37    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.21/1.37  thf('8', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 1.21/1.37      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.21/1.37  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 1.21/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.21/1.37  thf('10', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 1.21/1.37      inference('demod', [status(thm)], ['6', '9'])).
% 1.21/1.37  thf(t28_xboole_1, axiom,
% 1.21/1.37    (![A:$i,B:$i]:
% 1.21/1.37     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.21/1.37  thf('11', plain,
% 1.21/1.37      (![X4 : $i, X5 : $i]:
% 1.21/1.37         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.21/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.21/1.37  thf('12', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 1.21/1.37      inference('sup-', [status(thm)], ['10', '11'])).
% 1.21/1.37  thf(commutativity_k3_xboole_0, axiom,
% 1.21/1.37    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.21/1.37  thf('13', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.37  thf(t100_xboole_1, axiom,
% 1.21/1.37    (![A:$i,B:$i]:
% 1.21/1.37     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.21/1.37  thf('14', plain,
% 1.21/1.37      (![X2 : $i, X3 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X2 @ X3)
% 1.21/1.37           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.21/1.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.37  thf('15', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X0 @ X1)
% 1.21/1.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['13', '14'])).
% 1.21/1.37  thf('16', plain,
% 1.21/1.37      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup+', [status(thm)], ['12', '15'])).
% 1.21/1.37  thf('17', plain,
% 1.21/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf(d5_subset_1, axiom,
% 1.21/1.37    (![A:$i,B:$i]:
% 1.21/1.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.21/1.37       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.21/1.37  thf('18', plain,
% 1.21/1.37      (![X12 : $i, X13 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 1.21/1.37          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.21/1.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.21/1.37  thf('19', plain,
% 1.21/1.37      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup-', [status(thm)], ['17', '18'])).
% 1.21/1.37  thf('20', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.21/1.37      inference('sup-', [status(thm)], ['3', '4'])).
% 1.21/1.37  thf('21', plain,
% 1.21/1.37      (![X4 : $i, X5 : $i]:
% 1.21/1.37         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.21/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.21/1.37  thf('22', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.21/1.37      inference('sup-', [status(thm)], ['20', '21'])).
% 1.21/1.37  thf('23', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X0 @ X1)
% 1.21/1.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['13', '14'])).
% 1.21/1.37  thf('24', plain,
% 1.21/1.37      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup+', [status(thm)], ['22', '23'])).
% 1.21/1.37  thf('25', plain,
% 1.21/1.37      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['19', '24'])).
% 1.21/1.37  thf('26', plain,
% 1.21/1.37      (![X20 : $i]:
% 1.21/1.37         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.21/1.37  thf('27', plain,
% 1.21/1.37      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup+', [status(thm)], ['22', '23'])).
% 1.21/1.37  thf('28', plain,
% 1.21/1.37      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.21/1.37        | ~ (l1_struct_0 @ sk_A))),
% 1.21/1.37      inference('sup+', [status(thm)], ['26', '27'])).
% 1.21/1.37  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 1.21/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.21/1.37  thf('30', plain,
% 1.21/1.37      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['28', '29'])).
% 1.21/1.37  thf('31', plain,
% 1.21/1.37      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['25', '30'])).
% 1.21/1.37  thf('32', plain,
% 1.21/1.37      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('33', plain,
% 1.21/1.37      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('split', [status(esa)], ['32'])).
% 1.21/1.37  thf('34', plain,
% 1.21/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf(d4_tops_1, axiom,
% 1.21/1.37    (![A:$i]:
% 1.21/1.37     ( ( l1_pre_topc @ A ) =>
% 1.21/1.37       ( ![B:$i]:
% 1.21/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.37           ( ( v2_tops_1 @ B @ A ) <=>
% 1.21/1.37             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.21/1.37  thf('35', plain,
% 1.21/1.37      (![X28 : $i, X29 : $i]:
% 1.21/1.37         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.21/1.37          | ~ (v2_tops_1 @ X28 @ X29)
% 1.21/1.37          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 1.21/1.37          | ~ (l1_pre_topc @ X29))),
% 1.21/1.37      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.21/1.37  thf('36', plain,
% 1.21/1.37      ((~ (l1_pre_topc @ sk_A)
% 1.21/1.37        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.21/1.37        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.21/1.37      inference('sup-', [status(thm)], ['34', '35'])).
% 1.21/1.37  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('38', plain,
% 1.21/1.37      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.21/1.37        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.21/1.37      inference('demod', [status(thm)], ['36', '37'])).
% 1.21/1.37  thf('39', plain,
% 1.21/1.37      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['33', '38'])).
% 1.21/1.37  thf('40', plain,
% 1.21/1.37      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['31', '39'])).
% 1.21/1.37  thf('41', plain,
% 1.21/1.37      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['16', '40'])).
% 1.21/1.37  thf('42', plain,
% 1.21/1.37      (![X20 : $i]:
% 1.21/1.37         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.21/1.37  thf('43', plain,
% 1.21/1.37      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup+', [status(thm)], ['22', '23'])).
% 1.21/1.37  thf(t36_xboole_1, axiom,
% 1.21/1.37    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.21/1.37  thf('44', plain,
% 1.21/1.37      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.21/1.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.21/1.37  thf('45', plain,
% 1.21/1.37      (![X17 : $i, X19 : $i]:
% 1.21/1.37         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 1.21/1.37      inference('cnf', [status(esa)], [t3_subset])).
% 1.21/1.37  thf('46', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['44', '45'])).
% 1.21/1.37  thf('47', plain,
% 1.21/1.37      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['43', '46'])).
% 1.21/1.37  thf('48', plain,
% 1.21/1.37      (((m1_subset_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.21/1.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.21/1.37        | ~ (l1_struct_0 @ sk_A))),
% 1.21/1.37      inference('sup+', [status(thm)], ['42', '47'])).
% 1.21/1.37  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 1.21/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.21/1.37  thf('50', plain,
% 1.21/1.37      ((m1_subset_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['48', '49'])).
% 1.21/1.37  thf(d3_tops_1, axiom,
% 1.21/1.37    (![A:$i]:
% 1.21/1.37     ( ( l1_pre_topc @ A ) =>
% 1.21/1.37       ( ![B:$i]:
% 1.21/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.37           ( ( v1_tops_1 @ B @ A ) <=>
% 1.21/1.37             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 1.21/1.37  thf('51', plain,
% 1.21/1.37      (![X26 : $i, X27 : $i]:
% 1.21/1.37         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.21/1.37          | ~ (v1_tops_1 @ X26 @ X27)
% 1.21/1.37          | ((k2_pre_topc @ X27 @ X26) = (k2_struct_0 @ X27))
% 1.21/1.37          | ~ (l1_pre_topc @ X27))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.21/1.37  thf('52', plain,
% 1.21/1.37      ((~ (l1_pre_topc @ sk_A)
% 1.21/1.37        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.21/1.37            = (k2_struct_0 @ sk_A))
% 1.21/1.37        | ~ (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.21/1.37      inference('sup-', [status(thm)], ['50', '51'])).
% 1.21/1.37  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('54', plain,
% 1.21/1.37      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.21/1.37          = (k2_struct_0 @ sk_A))
% 1.21/1.37        | ~ (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.21/1.37      inference('demod', [status(thm)], ['52', '53'])).
% 1.21/1.37  thf('55', plain,
% 1.21/1.37      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.21/1.37          = (k2_struct_0 @ sk_A)))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['41', '54'])).
% 1.21/1.37  thf('56', plain,
% 1.21/1.37      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['43', '46'])).
% 1.21/1.37  thf(dt_k2_pre_topc, axiom,
% 1.21/1.37    (![A:$i,B:$i]:
% 1.21/1.37     ( ( ( l1_pre_topc @ A ) & 
% 1.21/1.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.21/1.37       ( m1_subset_1 @
% 1.21/1.37         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.21/1.37  thf('57', plain,
% 1.21/1.37      (![X21 : $i, X22 : $i]:
% 1.21/1.37         (~ (l1_pre_topc @ X21)
% 1.21/1.37          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.21/1.37          | (m1_subset_1 @ (k2_pre_topc @ X21 @ X22) @ 
% 1.21/1.37             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 1.21/1.37      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.21/1.37  thf('58', plain,
% 1.21/1.37      (((m1_subset_1 @ 
% 1.21/1.37         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.21/1.37        | ~ (l1_pre_topc @ sk_A))),
% 1.21/1.37      inference('sup-', [status(thm)], ['56', '57'])).
% 1.21/1.37  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('60', plain,
% 1.21/1.37      ((m1_subset_1 @ 
% 1.21/1.37        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['58', '59'])).
% 1.21/1.37  thf('61', plain,
% 1.21/1.37      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['28', '29'])).
% 1.21/1.37  thf('62', plain,
% 1.21/1.37      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup+', [status(thm)], ['12', '15'])).
% 1.21/1.37  thf('63', plain,
% 1.21/1.37      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['61', '62'])).
% 1.21/1.37  thf('64', plain,
% 1.21/1.37      ((m1_subset_1 @ 
% 1.21/1.37        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['60', '63'])).
% 1.21/1.37  thf('65', plain,
% 1.21/1.37      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.21/1.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['55', '64'])).
% 1.21/1.37  thf(involutiveness_k3_subset_1, axiom,
% 1.21/1.37    (![A:$i,B:$i]:
% 1.21/1.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.21/1.37       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.21/1.37  thf('66', plain,
% 1.21/1.37      (![X14 : $i, X15 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 1.21/1.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.21/1.37      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.21/1.37  thf('67', plain,
% 1.21/1.37      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.21/1.37          = (k2_struct_0 @ sk_A)))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['65', '66'])).
% 1.21/1.37  thf('68', plain,
% 1.21/1.37      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.21/1.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['55', '64'])).
% 1.21/1.37  thf('69', plain,
% 1.21/1.37      (![X12 : $i, X13 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 1.21/1.37          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.21/1.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.21/1.37  thf('70', plain,
% 1.21/1.37      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.21/1.37          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['68', '69'])).
% 1.21/1.37  thf('71', plain,
% 1.21/1.37      (![X20 : $i]:
% 1.21/1.37         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.21/1.37  thf('72', plain,
% 1.21/1.37      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.21/1.37          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['68', '69'])).
% 1.21/1.37  thf('73', plain,
% 1.21/1.37      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.21/1.37           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.21/1.37         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['71', '72'])).
% 1.21/1.37  thf(t46_xboole_1, axiom,
% 1.21/1.37    (![A:$i,B:$i]:
% 1.21/1.37     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.21/1.37  thf('74', plain,
% 1.21/1.37      (![X8 : $i, X9 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 1.21/1.37      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.21/1.37  thf('75', plain,
% 1.21/1.37      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.21/1.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.21/1.37  thf('76', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.21/1.37      inference('sup+', [status(thm)], ['74', '75'])).
% 1.21/1.37  thf('77', plain,
% 1.21/1.37      (![X4 : $i, X5 : $i]:
% 1.21/1.37         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.21/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.21/1.37  thf('78', plain,
% 1.21/1.37      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['76', '77'])).
% 1.21/1.37  thf('79', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X0 @ X1)
% 1.21/1.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['13', '14'])).
% 1.21/1.37  thf('80', plain,
% 1.21/1.37      (![X0 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['78', '79'])).
% 1.21/1.37  thf('81', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['44', '45'])).
% 1.21/1.37  thf('82', plain,
% 1.21/1.37      (![X0 : $i]:
% 1.21/1.37         (m1_subset_1 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['80', '81'])).
% 1.21/1.37  thf('83', plain,
% 1.21/1.37      (![X8 : $i, X9 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 1.21/1.37      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.21/1.37  thf('84', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['44', '45'])).
% 1.21/1.37  thf('85', plain,
% 1.21/1.37      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['83', '84'])).
% 1.21/1.37  thf('86', plain,
% 1.21/1.37      (![X12 : $i, X13 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 1.21/1.37          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.21/1.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.21/1.37  thf('87', plain,
% 1.21/1.37      (![X0 : $i]:
% 1.21/1.37         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['85', '86'])).
% 1.21/1.37  thf('88', plain,
% 1.21/1.37      (![X0 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['78', '79'])).
% 1.21/1.37  thf('89', plain,
% 1.21/1.37      (![X0 : $i]:
% 1.21/1.37         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('demod', [status(thm)], ['87', '88'])).
% 1.21/1.37  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.21/1.37  thf('90', plain, (![X10 : $i]: ((k1_subset_1 @ X10) = (k1_xboole_0))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.21/1.37  thf(t22_subset_1, axiom,
% 1.21/1.37    (![A:$i]:
% 1.21/1.37     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.21/1.37  thf('91', plain,
% 1.21/1.37      (![X16 : $i]:
% 1.21/1.37         ((k2_subset_1 @ X16) = (k3_subset_1 @ X16 @ (k1_subset_1 @ X16)))),
% 1.21/1.37      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.21/1.37  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.21/1.37  thf('92', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 1.21/1.37      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.21/1.37  thf('93', plain,
% 1.21/1.37      (![X16 : $i]: ((X16) = (k3_subset_1 @ X16 @ (k1_subset_1 @ X16)))),
% 1.21/1.37      inference('demod', [status(thm)], ['91', '92'])).
% 1.21/1.37  thf('94', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['90', '93'])).
% 1.21/1.37  thf('95', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['89', '94'])).
% 1.21/1.37  thf('96', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('demod', [status(thm)], ['82', '95'])).
% 1.21/1.37  thf('97', plain,
% 1.21/1.37      (![X12 : $i, X13 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 1.21/1.37          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.21/1.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.21/1.37  thf('98', plain,
% 1.21/1.37      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['96', '97'])).
% 1.21/1.37  thf('99', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('demod', [status(thm)], ['82', '95'])).
% 1.21/1.37  thf('100', plain,
% 1.21/1.37      (![X17 : $i, X18 : $i]:
% 1.21/1.37         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.21/1.37      inference('cnf', [status(esa)], [t3_subset])).
% 1.21/1.37  thf('101', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.21/1.37      inference('sup-', [status(thm)], ['99', '100'])).
% 1.21/1.37  thf('102', plain,
% 1.21/1.37      (![X4 : $i, X5 : $i]:
% 1.21/1.37         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.21/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.21/1.37  thf('103', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['101', '102'])).
% 1.21/1.37  thf('104', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X0 @ X1)
% 1.21/1.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['13', '14'])).
% 1.21/1.37  thf('105', plain,
% 1.21/1.37      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['103', '104'])).
% 1.21/1.37  thf('106', plain,
% 1.21/1.37      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.37      inference('demod', [status(thm)], ['98', '105'])).
% 1.21/1.37  thf('107', plain,
% 1.21/1.37      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['96', '97'])).
% 1.21/1.37  thf('108', plain,
% 1.21/1.37      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['83', '84'])).
% 1.21/1.37  thf('109', plain,
% 1.21/1.37      (![X14 : $i, X15 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 1.21/1.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.21/1.37      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.21/1.37  thf('110', plain,
% 1.21/1.37      (![X0 : $i]:
% 1.21/1.37         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['108', '109'])).
% 1.21/1.37  thf('111', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['90', '93'])).
% 1.21/1.37  thf('112', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.21/1.37      inference('demod', [status(thm)], ['110', '111'])).
% 1.21/1.37  thf('113', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['107', '112'])).
% 1.21/1.37  thf('114', plain,
% 1.21/1.37      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['103', '104'])).
% 1.21/1.37  thf('115', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.21/1.37      inference('demod', [status(thm)], ['113', '114'])).
% 1.21/1.37  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 1.21/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.21/1.37  thf('117', plain,
% 1.21/1.37      ((((k1_xboole_0)
% 1.21/1.37          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['73', '106', '115', '116'])).
% 1.21/1.37  thf('118', plain,
% 1.21/1.37      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.21/1.37          = (k1_xboole_0)))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['70', '117'])).
% 1.21/1.37  thf('119', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['90', '93'])).
% 1.21/1.37  thf('120', plain,
% 1.21/1.37      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['67', '118', '119'])).
% 1.21/1.37  thf('121', plain,
% 1.21/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf(d1_tops_1, axiom,
% 1.21/1.37    (![A:$i]:
% 1.21/1.37     ( ( l1_pre_topc @ A ) =>
% 1.21/1.37       ( ![B:$i]:
% 1.21/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.37           ( ( k1_tops_1 @ A @ B ) =
% 1.21/1.37             ( k3_subset_1 @
% 1.21/1.37               ( u1_struct_0 @ A ) @ 
% 1.21/1.37               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.21/1.37  thf('122', plain,
% 1.21/1.37      (![X24 : $i, X25 : $i]:
% 1.21/1.37         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.21/1.37          | ((k1_tops_1 @ X25 @ X24)
% 1.21/1.37              = (k3_subset_1 @ (u1_struct_0 @ X25) @ 
% 1.21/1.37                 (k2_pre_topc @ X25 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24))))
% 1.21/1.37          | ~ (l1_pre_topc @ X25))),
% 1.21/1.37      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.21/1.37  thf('123', plain,
% 1.21/1.37      ((~ (l1_pre_topc @ sk_A)
% 1.21/1.37        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.21/1.37            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37               (k2_pre_topc @ sk_A @ 
% 1.21/1.37                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.21/1.37      inference('sup-', [status(thm)], ['121', '122'])).
% 1.21/1.37  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('125', plain,
% 1.21/1.37      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['19', '24'])).
% 1.21/1.37  thf('126', plain,
% 1.21/1.37      (((k1_tops_1 @ sk_A @ sk_B)
% 1.21/1.37         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.21/1.37      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.21/1.37  thf('127', plain,
% 1.21/1.37      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['61', '62'])).
% 1.21/1.37  thf('128', plain,
% 1.21/1.37      (((k1_tops_1 @ sk_A @ sk_B)
% 1.21/1.37         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.21/1.37      inference('demod', [status(thm)], ['126', '127'])).
% 1.21/1.37  thf('129', plain,
% 1.21/1.37      ((((k1_tops_1 @ sk_A @ sk_B)
% 1.21/1.37          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.21/1.37             (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['120', '128'])).
% 1.21/1.37  thf('130', plain,
% 1.21/1.37      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.21/1.37          = (k2_struct_0 @ sk_A)))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['41', '54'])).
% 1.21/1.37  thf('131', plain,
% 1.21/1.37      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.21/1.37      inference('demod', [status(thm)], ['98', '105'])).
% 1.21/1.37  thf('132', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.21/1.37      inference('demod', [status(thm)], ['113', '114'])).
% 1.21/1.37  thf('133', plain,
% 1.21/1.37      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.21/1.37         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 1.21/1.37  thf('134', plain,
% 1.21/1.37      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 1.21/1.37         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('split', [status(esa)], ['0'])).
% 1.21/1.37  thf('135', plain,
% 1.21/1.37      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.21/1.37         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 1.21/1.37             ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['133', '134'])).
% 1.21/1.37  thf('136', plain,
% 1.21/1.37      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.21/1.37       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.21/1.37      inference('simplify', [status(thm)], ['135'])).
% 1.21/1.37  thf('137', plain,
% 1.21/1.37      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.21/1.37       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.21/1.37      inference('split', [status(esa)], ['32'])).
% 1.21/1.37  thf('138', plain,
% 1.21/1.37      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('split', [status(esa)], ['32'])).
% 1.21/1.37  thf('139', plain,
% 1.21/1.37      ((m1_subset_1 @ 
% 1.21/1.37        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['60', '63'])).
% 1.21/1.37  thf('140', plain,
% 1.21/1.37      (![X14 : $i, X15 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 1.21/1.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.21/1.37      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.21/1.37  thf('141', plain,
% 1.21/1.37      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37          (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.21/1.37         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['139', '140'])).
% 1.21/1.37  thf('142', plain,
% 1.21/1.37      ((m1_subset_1 @ 
% 1.21/1.37        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['60', '63'])).
% 1.21/1.37  thf('143', plain,
% 1.21/1.37      (![X12 : $i, X13 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 1.21/1.37          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.21/1.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.21/1.37  thf('144', plain,
% 1.21/1.37      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 1.21/1.37         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.21/1.37      inference('sup-', [status(thm)], ['142', '143'])).
% 1.21/1.37  thf('145', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['44', '45'])).
% 1.21/1.37  thf('146', plain,
% 1.21/1.37      (![X12 : $i, X13 : $i]:
% 1.21/1.37         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 1.21/1.37          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.21/1.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.21/1.37  thf('147', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.21/1.37           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['145', '146'])).
% 1.21/1.37  thf('148', plain,
% 1.21/1.37      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.21/1.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.21/1.37  thf('149', plain,
% 1.21/1.37      (![X4 : $i, X5 : $i]:
% 1.21/1.37         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.21/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.21/1.37  thf('150', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.21/1.37           = (k4_xboole_0 @ X0 @ X1))),
% 1.21/1.37      inference('sup-', [status(thm)], ['148', '149'])).
% 1.21/1.37  thf('151', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.37  thf('152', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.21/1.37           = (k4_xboole_0 @ X0 @ X1))),
% 1.21/1.37      inference('demod', [status(thm)], ['150', '151'])).
% 1.21/1.37  thf('153', plain,
% 1.21/1.37      (![X2 : $i, X3 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X2 @ X3)
% 1.21/1.37           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.21/1.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.37  thf('154', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.21/1.37           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['152', '153'])).
% 1.21/1.37  thf('155', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]:
% 1.21/1.37         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.21/1.37           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.21/1.37      inference('demod', [status(thm)], ['147', '154'])).
% 1.21/1.37  thf('156', plain,
% 1.21/1.37      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37          (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.21/1.37         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.21/1.37      inference('demod', [status(thm)], ['141', '144', '155'])).
% 1.21/1.37  thf('157', plain,
% 1.21/1.37      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 1.21/1.37         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.21/1.37      inference('sup-', [status(thm)], ['142', '143'])).
% 1.21/1.37  thf('158', plain,
% 1.21/1.37      (((k1_tops_1 @ sk_A @ sk_B)
% 1.21/1.37         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.21/1.37      inference('demod', [status(thm)], ['126', '127'])).
% 1.21/1.37  thf('159', plain,
% 1.21/1.37      (((k1_tops_1 @ sk_A @ sk_B)
% 1.21/1.37         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.37            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.21/1.37      inference('sup+', [status(thm)], ['157', '158'])).
% 1.21/1.37  thf('160', plain,
% 1.21/1.37      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.21/1.37         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.21/1.37      inference('demod', [status(thm)], ['156', '159'])).
% 1.21/1.37  thf('161', plain,
% 1.21/1.37      ((((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.21/1.37          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('sup+', [status(thm)], ['138', '160'])).
% 1.21/1.37  thf('162', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.37      inference('sup+', [status(thm)], ['89', '94'])).
% 1.21/1.37  thf('163', plain,
% 1.21/1.37      ((((u1_struct_0 @ sk_A)
% 1.21/1.37          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('demod', [status(thm)], ['161', '162'])).
% 1.21/1.37  thf('164', plain,
% 1.21/1.37      (![X20 : $i]:
% 1.21/1.37         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.21/1.37  thf('165', plain,
% 1.21/1.37      ((((u1_struct_0 @ sk_A)
% 1.21/1.37          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('demod', [status(thm)], ['161', '162'])).
% 1.21/1.37  thf('166', plain,
% 1.21/1.37      (![X20 : $i]:
% 1.21/1.37         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.21/1.37  thf('167', plain,
% 1.21/1.37      ((m1_subset_1 @ 
% 1.21/1.37        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['60', '63'])).
% 1.21/1.37  thf('168', plain,
% 1.21/1.37      (![X17 : $i, X18 : $i]:
% 1.21/1.37         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.21/1.37      inference('cnf', [status(esa)], [t3_subset])).
% 1.21/1.37  thf('169', plain,
% 1.21/1.37      ((r1_tarski @ 
% 1.21/1.37        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37        (u1_struct_0 @ sk_A))),
% 1.21/1.37      inference('sup-', [status(thm)], ['167', '168'])).
% 1.21/1.37  thf('170', plain,
% 1.21/1.37      (((r1_tarski @ 
% 1.21/1.37         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37         (k2_struct_0 @ sk_A))
% 1.21/1.37        | ~ (l1_struct_0 @ sk_A))),
% 1.21/1.37      inference('sup+', [status(thm)], ['166', '169'])).
% 1.21/1.37  thf('171', plain, ((l1_struct_0 @ sk_A)),
% 1.21/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.21/1.37  thf('172', plain,
% 1.21/1.37      ((r1_tarski @ 
% 1.21/1.37        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.21/1.37        (k2_struct_0 @ sk_A))),
% 1.21/1.37      inference('demod', [status(thm)], ['170', '171'])).
% 1.21/1.37  thf('173', plain,
% 1.21/1.37      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('sup+', [status(thm)], ['165', '172'])).
% 1.21/1.37  thf('174', plain,
% 1.21/1.37      (![X4 : $i, X5 : $i]:
% 1.21/1.37         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.21/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.21/1.37  thf('175', plain,
% 1.21/1.37      ((((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.21/1.37          = (u1_struct_0 @ sk_A)))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('sup-', [status(thm)], ['173', '174'])).
% 1.21/1.37  thf('176', plain,
% 1.21/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.37  thf('177', plain,
% 1.21/1.37      ((((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.21/1.37          = (u1_struct_0 @ sk_A)))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('demod', [status(thm)], ['175', '176'])).
% 1.21/1.37  thf('178', plain,
% 1.21/1.37      (((((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.21/1.37           = (u1_struct_0 @ sk_A))
% 1.21/1.37         | ~ (l1_struct_0 @ sk_A)))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('sup+', [status(thm)], ['164', '177'])).
% 1.21/1.37  thf('179', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.37      inference('sup-', [status(thm)], ['101', '102'])).
% 1.21/1.37  thf('180', plain, ((l1_struct_0 @ sk_A)),
% 1.21/1.37      inference('sup-', [status(thm)], ['7', '8'])).
% 1.21/1.37  thf('181', plain,
% 1.21/1.37      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('demod', [status(thm)], ['178', '179', '180'])).
% 1.21/1.37  thf('182', plain,
% 1.21/1.37      ((((k2_struct_0 @ sk_A)
% 1.21/1.37          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('demod', [status(thm)], ['163', '181'])).
% 1.21/1.37  thf('183', plain,
% 1.21/1.37      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('sup+', [status(thm)], ['43', '46'])).
% 1.21/1.37  thf('184', plain,
% 1.21/1.37      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['28', '29'])).
% 1.21/1.37  thf('185', plain,
% 1.21/1.37      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.21/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['183', '184'])).
% 1.21/1.37  thf('186', plain,
% 1.21/1.37      (![X26 : $i, X27 : $i]:
% 1.21/1.37         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.21/1.37          | ((k2_pre_topc @ X27 @ X26) != (k2_struct_0 @ X27))
% 1.21/1.37          | (v1_tops_1 @ X26 @ X27)
% 1.21/1.37          | ~ (l1_pre_topc @ X27))),
% 1.21/1.37      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.21/1.37  thf('187', plain,
% 1.21/1.37      ((~ (l1_pre_topc @ sk_A)
% 1.21/1.37        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.21/1.37        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.21/1.37            != (k2_struct_0 @ sk_A)))),
% 1.21/1.37      inference('sup-', [status(thm)], ['185', '186'])).
% 1.21/1.37  thf('188', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('189', plain,
% 1.21/1.37      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.21/1.37        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.21/1.37            != (k2_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['187', '188'])).
% 1.21/1.37  thf('190', plain,
% 1.21/1.37      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup+', [status(thm)], ['12', '15'])).
% 1.21/1.37  thf('191', plain,
% 1.21/1.37      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup+', [status(thm)], ['12', '15'])).
% 1.21/1.37  thf('192', plain,
% 1.21/1.37      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.21/1.37        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.21/1.37            != (k2_struct_0 @ sk_A)))),
% 1.21/1.37      inference('demod', [status(thm)], ['189', '190', '191'])).
% 1.21/1.37  thf('193', plain,
% 1.21/1.37      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 1.21/1.37         | (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('sup-', [status(thm)], ['182', '192'])).
% 1.21/1.37  thf('194', plain,
% 1.21/1.37      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('simplify', [status(thm)], ['193'])).
% 1.21/1.37  thf('195', plain,
% 1.21/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('196', plain,
% 1.21/1.37      (![X28 : $i, X29 : $i]:
% 1.21/1.37         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.21/1.37          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 1.21/1.37          | (v2_tops_1 @ X28 @ X29)
% 1.21/1.37          | ~ (l1_pre_topc @ X29))),
% 1.21/1.37      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.21/1.37  thf('197', plain,
% 1.21/1.37      ((~ (l1_pre_topc @ sk_A)
% 1.21/1.37        | (v2_tops_1 @ sk_B @ sk_A)
% 1.21/1.37        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.21/1.37      inference('sup-', [status(thm)], ['195', '196'])).
% 1.21/1.37  thf('198', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.37  thf('199', plain,
% 1.21/1.37      (((v2_tops_1 @ sk_B @ sk_A)
% 1.21/1.37        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.21/1.37      inference('demod', [status(thm)], ['197', '198'])).
% 1.21/1.37  thf('200', plain,
% 1.21/1.37      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('demod', [status(thm)], ['25', '30'])).
% 1.21/1.37  thf('201', plain,
% 1.21/1.37      (((v2_tops_1 @ sk_B @ sk_A)
% 1.21/1.37        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.21/1.37      inference('demod', [status(thm)], ['199', '200'])).
% 1.21/1.37  thf('202', plain,
% 1.21/1.37      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.21/1.37         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.21/1.37      inference('sup+', [status(thm)], ['12', '15'])).
% 1.21/1.37  thf('203', plain,
% 1.21/1.37      (((v2_tops_1 @ sk_B @ sk_A)
% 1.21/1.37        | ~ (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.21/1.37      inference('demod', [status(thm)], ['201', '202'])).
% 1.21/1.37  thf('204', plain,
% 1.21/1.37      (((v2_tops_1 @ sk_B @ sk_A))
% 1.21/1.37         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.21/1.37      inference('sup-', [status(thm)], ['194', '203'])).
% 1.21/1.37  thf('205', plain,
% 1.21/1.37      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.21/1.37      inference('split', [status(esa)], ['0'])).
% 1.21/1.37  thf('206', plain,
% 1.21/1.37      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.21/1.37       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.21/1.37      inference('sup-', [status(thm)], ['204', '205'])).
% 1.21/1.37  thf('207', plain, ($false),
% 1.21/1.37      inference('sat_resolution*', [status(thm)], ['1', '136', '137', '206'])).
% 1.21/1.37  
% 1.21/1.37  % SZS output end Refutation
% 1.21/1.37  
% 1.21/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
