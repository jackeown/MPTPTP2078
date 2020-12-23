%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4uAE5AawHN

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:13 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  180 (1029 expanded)
%              Number of leaves         :   31 ( 316 expanded)
%              Depth                    :   25
%              Number of atoms          : 1472 (9321 expanded)
%              Number of equality atoms :  109 ( 670 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X45: $i] :
      ( ( ( k2_struct_0 @ X45 )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X45: $i] :
      ( ( ( k2_struct_0 @ X45 )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v2_tops_1 @ X53 @ X54 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 ) @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X45: $i] :
      ( ( ( k2_struct_0 @ X45 )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('15',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X48: $i] :
      ( ( l1_struct_0 @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X45: $i] :
      ( ( ( k2_struct_0 @ X45 )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','28'])).

thf('30',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('35',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v1_tops_1 @ X51 @ X52 )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = ( k2_struct_0 @ X52 ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['3','48'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X38 ) @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('51',plain,(
    ! [X35: $i] :
      ( ( k2_subset_1 @ X35 )
      = X35 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('52',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('61',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','59','60'])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('63',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('70',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k1_tops_1 @ X50 @ X49 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X50 ) @ ( k2_pre_topc @ X50 @ ( k3_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 ) ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('76',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','58'])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('85',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('86',plain,(
    ! [X45: $i] :
      ( ( ( k2_struct_0 @ X45 )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('88',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('89',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('91',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('93',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('96',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X45: $i] :
      ( ( ( k2_struct_0 @ X45 )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('101',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('103',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','103'])).

thf('105',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','104'])).

thf('106',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('107',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('108',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_subset_1 @ X42 @ ( k3_subset_1 @ X42 @ X41 ) )
        = X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','58'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('113',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','58'])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['111','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['111','118'])).

thf('121',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106','119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('123',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_subset_1 @ X42 @ ( k3_subset_1 @ X42 @ X41 ) )
        = X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('124',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('126',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('130',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('132',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k2_pre_topc @ X52 @ X51 )
       != ( k2_struct_0 @ X52 ) )
      | ( v1_tops_1 @ X51 @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('133',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 ) @ X54 )
      | ( v2_tops_1 @ X53 @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('140',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('143',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','143'])).

thf('145',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('146',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','83','84','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4uAE5AawHN
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.06  % Solved by: fo/fo7.sh
% 0.83/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.06  % done 1600 iterations in 0.604s
% 0.83/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.06  % SZS output start Refutation
% 0.83/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.83/1.06  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.83/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.06  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.83/1.06  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.83/1.06  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.83/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.06  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.83/1.06  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.83/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.06  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.83/1.06  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.83/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.06  thf(t84_tops_1, conjecture,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( l1_pre_topc @ A ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06           ( ( v2_tops_1 @ B @ A ) <=>
% 0.83/1.06             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.83/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.06    (~( ![A:$i]:
% 0.83/1.06        ( ( l1_pre_topc @ A ) =>
% 0.83/1.06          ( ![B:$i]:
% 0.83/1.06            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06              ( ( v2_tops_1 @ B @ A ) <=>
% 0.83/1.06                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.83/1.06    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.83/1.06  thf('0', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.83/1.06        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('1', plain,
% 0.83/1.06      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.83/1.06       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.83/1.06      inference('split', [status(esa)], ['0'])).
% 0.83/1.06  thf(d3_struct_0, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.83/1.06  thf('2', plain,
% 0.83/1.06      (![X45 : $i]:
% 0.83/1.06         (((k2_struct_0 @ X45) = (u1_struct_0 @ X45)) | ~ (l1_struct_0 @ X45))),
% 0.83/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.06  thf('3', plain,
% 0.83/1.06      (![X45 : $i]:
% 0.83/1.06         (((k2_struct_0 @ X45) = (u1_struct_0 @ X45)) | ~ (l1_struct_0 @ X45))),
% 0.83/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.06  thf('4', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('5', plain,
% 0.83/1.06      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('split', [status(esa)], ['4'])).
% 0.83/1.06  thf('6', plain,
% 0.83/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf(d4_tops_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( l1_pre_topc @ A ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06           ( ( v2_tops_1 @ B @ A ) <=>
% 0.83/1.06             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.83/1.06  thf('7', plain,
% 0.83/1.06      (![X53 : $i, X54 : $i]:
% 0.83/1.06         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.83/1.06          | ~ (v2_tops_1 @ X53 @ X54)
% 0.83/1.06          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X54) @ X53) @ X54)
% 0.83/1.06          | ~ (l1_pre_topc @ X54))),
% 0.83/1.06      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.83/1.06  thf('8', plain,
% 0.83/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.06        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.83/1.06        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.83/1.06      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.06  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('10', plain,
% 0.83/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf(d5_subset_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.06       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.83/1.06  thf('11', plain,
% 0.83/1.06      (![X36 : $i, X37 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.83/1.06          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.83/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.83/1.06  thf('12', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('sup-', [status(thm)], ['10', '11'])).
% 0.83/1.06  thf('13', plain,
% 0.83/1.06      (![X45 : $i]:
% 0.83/1.06         (((k2_struct_0 @ X45) = (u1_struct_0 @ X45)) | ~ (l1_struct_0 @ X45))),
% 0.83/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.06  thf('14', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('sup-', [status(thm)], ['10', '11'])).
% 0.83/1.06  thf('15', plain,
% 0.83/1.06      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.83/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.06      inference('sup+', [status(thm)], ['13', '14'])).
% 0.83/1.06  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf(dt_l1_pre_topc, axiom,
% 0.83/1.06    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.83/1.06  thf('17', plain,
% 0.83/1.06      (![X48 : $i]: ((l1_struct_0 @ X48) | ~ (l1_pre_topc @ X48))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.83/1.06  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.06      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.06  thf('19', plain,
% 0.83/1.06      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('demod', [status(thm)], ['15', '18'])).
% 0.83/1.06  thf('20', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('demod', [status(thm)], ['12', '19'])).
% 0.83/1.06  thf('21', plain,
% 0.83/1.06      (![X45 : $i]:
% 0.83/1.06         (((k2_struct_0 @ X45) = (u1_struct_0 @ X45)) | ~ (l1_struct_0 @ X45))),
% 0.83/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.06  thf('22', plain,
% 0.83/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('23', plain,
% 0.83/1.06      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.06      inference('sup+', [status(thm)], ['21', '22'])).
% 0.83/1.06  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.06      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.06  thf('25', plain,
% 0.83/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['23', '24'])).
% 0.83/1.06  thf('26', plain,
% 0.83/1.06      (![X36 : $i, X37 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.83/1.06          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.83/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.83/1.06  thf('27', plain,
% 0.83/1.06      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('sup-', [status(thm)], ['25', '26'])).
% 0.83/1.06  thf('28', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('demod', [status(thm)], ['20', '27'])).
% 0.83/1.06  thf('29', plain,
% 0.83/1.06      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.83/1.06        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.83/1.06      inference('demod', [status(thm)], ['8', '9', '28'])).
% 0.83/1.06  thf('30', plain,
% 0.83/1.06      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['5', '29'])).
% 0.83/1.06  thf('31', plain,
% 0.83/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf(dt_k3_subset_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.06       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.83/1.06  thf('32', plain,
% 0.83/1.06      (![X39 : $i, X40 : $i]:
% 0.83/1.06         ((m1_subset_1 @ (k3_subset_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39))
% 0.83/1.06          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.83/1.06  thf('33', plain,
% 0.83/1.06      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['31', '32'])).
% 0.83/1.06  thf('34', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('demod', [status(thm)], ['20', '27'])).
% 0.83/1.06  thf('35', plain,
% 0.83/1.06      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['33', '34'])).
% 0.83/1.06  thf(d3_tops_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( l1_pre_topc @ A ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06           ( ( v1_tops_1 @ B @ A ) <=>
% 0.83/1.06             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.83/1.06  thf('36', plain,
% 0.83/1.06      (![X51 : $i, X52 : $i]:
% 0.83/1.06         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.83/1.06          | ~ (v1_tops_1 @ X51 @ X52)
% 0.83/1.06          | ((k2_pre_topc @ X52 @ X51) = (k2_struct_0 @ X52))
% 0.83/1.06          | ~ (l1_pre_topc @ X52))),
% 0.83/1.06      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.83/1.06  thf('37', plain,
% 0.83/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.06        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.83/1.06            = (k2_struct_0 @ sk_A))
% 0.83/1.06        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.83/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.83/1.06  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('39', plain,
% 0.83/1.06      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.83/1.06          = (k2_struct_0 @ sk_A))
% 0.83/1.06        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.83/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.83/1.06  thf('40', plain,
% 0.83/1.06      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.83/1.06          = (k2_struct_0 @ sk_A)))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['30', '39'])).
% 0.83/1.06  thf('41', plain,
% 0.83/1.06      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['33', '34'])).
% 0.83/1.06  thf(dt_k2_pre_topc, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( ( l1_pre_topc @ A ) & 
% 0.83/1.06         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.83/1.06       ( m1_subset_1 @
% 0.83/1.06         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.83/1.06  thf('42', plain,
% 0.83/1.06      (![X46 : $i, X47 : $i]:
% 0.83/1.06         (~ (l1_pre_topc @ X46)
% 0.83/1.06          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.83/1.06          | (m1_subset_1 @ (k2_pre_topc @ X46 @ X47) @ 
% 0.83/1.06             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.83/1.06  thf('43', plain,
% 0.83/1.06      (((m1_subset_1 @ 
% 0.83/1.06         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.83/1.06         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.06      inference('sup-', [status(thm)], ['41', '42'])).
% 0.83/1.06  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('45', plain,
% 0.83/1.06      ((m1_subset_1 @ 
% 0.83/1.06        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.06  thf('46', plain,
% 0.83/1.06      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.06         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup+', [status(thm)], ['40', '45'])).
% 0.83/1.06  thf('47', plain,
% 0.83/1.06      (![X36 : $i, X37 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.83/1.06          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.83/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.83/1.06  thf('48', plain,
% 0.83/1.06      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.83/1.06          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['46', '47'])).
% 0.83/1.06  thf('49', plain,
% 0.83/1.06      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.83/1.06           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.83/1.06         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup+', [status(thm)], ['3', '48'])).
% 0.83/1.06  thf(dt_k2_subset_1, axiom,
% 0.83/1.06    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.83/1.06  thf('50', plain,
% 0.83/1.06      (![X38 : $i]: (m1_subset_1 @ (k2_subset_1 @ X38) @ (k1_zfmisc_1 @ X38))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.83/1.06  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.83/1.06  thf('51', plain, (![X35 : $i]: ((k2_subset_1 @ X35) = (X35))),
% 0.83/1.06      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.83/1.06  thf('52', plain, (![X38 : $i]: (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X38))),
% 0.83/1.06      inference('demod', [status(thm)], ['50', '51'])).
% 0.83/1.06  thf('53', plain,
% 0.83/1.06      (![X36 : $i, X37 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.83/1.06          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.83/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.83/1.06  thf('54', plain,
% 0.83/1.06      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['52', '53'])).
% 0.83/1.06  thf(d10_xboole_0, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/1.06  thf('55', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.83/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.06  thf('56', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.06      inference('simplify', [status(thm)], ['55'])).
% 0.83/1.06  thf(l32_xboole_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.06  thf('57', plain,
% 0.83/1.06      (![X3 : $i, X5 : $i]:
% 0.83/1.06         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.83/1.06      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.83/1.06  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['56', '57'])).
% 0.83/1.06  thf('59', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.06      inference('demod', [status(thm)], ['54', '58'])).
% 0.83/1.06  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.06      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.06  thf('61', plain,
% 0.83/1.06      ((((k1_xboole_0)
% 0.83/1.06          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['49', '59', '60'])).
% 0.83/1.06  thf('62', plain,
% 0.83/1.06      (![X3 : $i, X4 : $i]:
% 0.83/1.06         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.83/1.06      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.83/1.06  thf('63', plain,
% 0.83/1.06      (((((k1_xboole_0) != (k1_xboole_0))
% 0.83/1.06         | (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['61', '62'])).
% 0.83/1.06  thf('64', plain,
% 0.83/1.06      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('simplify', [status(thm)], ['63'])).
% 0.83/1.06  thf('65', plain,
% 0.83/1.06      (![X0 : $i, X2 : $i]:
% 0.83/1.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.83/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.06  thf('66', plain,
% 0.83/1.06      (((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.06         | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['64', '65'])).
% 0.83/1.06  thf('67', plain,
% 0.83/1.06      (((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.83/1.06         | ~ (l1_struct_0 @ sk_A)
% 0.83/1.06         | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['2', '66'])).
% 0.83/1.06  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.06      inference('simplify', [status(thm)], ['55'])).
% 0.83/1.06  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.06      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.06  thf('70', plain,
% 0.83/1.06      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.83/1.06  thf('71', plain,
% 0.83/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf(d1_tops_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( l1_pre_topc @ A ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06           ( ( k1_tops_1 @ A @ B ) =
% 0.83/1.06             ( k3_subset_1 @
% 0.83/1.06               ( u1_struct_0 @ A ) @ 
% 0.83/1.06               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.83/1.06  thf('72', plain,
% 0.83/1.06      (![X49 : $i, X50 : $i]:
% 0.83/1.06         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.83/1.06          | ((k1_tops_1 @ X50 @ X49)
% 0.83/1.06              = (k3_subset_1 @ (u1_struct_0 @ X50) @ 
% 0.83/1.06                 (k2_pre_topc @ X50 @ (k3_subset_1 @ (u1_struct_0 @ X50) @ X49))))
% 0.83/1.06          | ~ (l1_pre_topc @ X50))),
% 0.83/1.06      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.83/1.06  thf('73', plain,
% 0.83/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.06        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.83/1.06            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.06               (k2_pre_topc @ sk_A @ 
% 0.83/1.06                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.83/1.06      inference('sup-', [status(thm)], ['71', '72'])).
% 0.83/1.06  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('75', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('demod', [status(thm)], ['20', '27'])).
% 0.83/1.06  thf('76', plain,
% 0.83/1.06      (((k1_tops_1 @ sk_A @ sk_B)
% 0.83/1.06         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.06            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.83/1.06      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.83/1.06  thf('77', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.83/1.06          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.06             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup+', [status(thm)], ['70', '76'])).
% 0.83/1.06  thf('78', plain,
% 0.83/1.06      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.83/1.06          = (k2_struct_0 @ sk_A)))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['30', '39'])).
% 0.83/1.06  thf('79', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.06      inference('demod', [status(thm)], ['54', '58'])).
% 0.83/1.06  thf('80', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.83/1.06         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.83/1.06  thf('81', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.83/1.06         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('split', [status(esa)], ['0'])).
% 0.83/1.06  thf('82', plain,
% 0.83/1.06      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.83/1.06         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.83/1.06             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['80', '81'])).
% 0.83/1.06  thf('83', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.83/1.06       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.83/1.06      inference('simplify', [status(thm)], ['82'])).
% 0.83/1.06  thf('84', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.83/1.06       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.83/1.06      inference('split', [status(esa)], ['4'])).
% 0.83/1.06  thf('85', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('split', [status(esa)], ['4'])).
% 0.83/1.06  thf('86', plain,
% 0.83/1.06      (![X45 : $i]:
% 0.83/1.06         (((k2_struct_0 @ X45) = (u1_struct_0 @ X45)) | ~ (l1_struct_0 @ X45))),
% 0.83/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.06  thf('87', plain,
% 0.83/1.06      ((m1_subset_1 @ 
% 0.83/1.06        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.06  thf('88', plain,
% 0.83/1.06      (![X39 : $i, X40 : $i]:
% 0.83/1.06         ((m1_subset_1 @ (k3_subset_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39))
% 0.83/1.06          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.83/1.06  thf('89', plain,
% 0.83/1.06      ((m1_subset_1 @ 
% 0.83/1.06        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.06         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['87', '88'])).
% 0.83/1.06  thf('90', plain,
% 0.83/1.06      (((k1_tops_1 @ sk_A @ sk_B)
% 0.83/1.06         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.06            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.83/1.06      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.83/1.06  thf('91', plain,
% 0.83/1.06      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['89', '90'])).
% 0.83/1.06  thf('92', plain,
% 0.83/1.06      (![X36 : $i, X37 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.83/1.06          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.83/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.83/1.06  thf('93', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.06         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['91', '92'])).
% 0.83/1.06  thf('94', plain,
% 0.83/1.06      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.06          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.83/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.06      inference('sup+', [status(thm)], ['86', '93'])).
% 0.83/1.06  thf('95', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.06      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.06  thf('96', plain,
% 0.83/1.06      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.06         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.83/1.06      inference('demod', [status(thm)], ['94', '95'])).
% 0.83/1.06  thf('97', plain,
% 0.83/1.06      (![X45 : $i]:
% 0.83/1.06         (((k2_struct_0 @ X45) = (u1_struct_0 @ X45)) | ~ (l1_struct_0 @ X45))),
% 0.83/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.06  thf('98', plain,
% 0.83/1.06      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['89', '90'])).
% 0.83/1.06  thf('99', plain,
% 0.83/1.06      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.83/1.06         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.06      inference('sup+', [status(thm)], ['97', '98'])).
% 0.83/1.06  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.06      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.06  thf('101', plain,
% 0.83/1.06      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['99', '100'])).
% 0.83/1.06  thf('102', plain,
% 0.83/1.06      (![X36 : $i, X37 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.83/1.06          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.83/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.83/1.06  thf('103', plain,
% 0.83/1.06      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.06         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['101', '102'])).
% 0.83/1.06  thf('104', plain,
% 0.83/1.06      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.06         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.83/1.06      inference('demod', [status(thm)], ['96', '103'])).
% 0.83/1.06  thf('105', plain,
% 0.83/1.06      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.06          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('sup+', [status(thm)], ['85', '104'])).
% 0.83/1.06  thf('106', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('split', [status(esa)], ['4'])).
% 0.83/1.06  thf('107', plain, (![X38 : $i]: (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X38))),
% 0.83/1.06      inference('demod', [status(thm)], ['50', '51'])).
% 0.83/1.06  thf(involutiveness_k3_subset_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.06       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.83/1.06  thf('108', plain,
% 0.83/1.06      (![X41 : $i, X42 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X42 @ (k3_subset_1 @ X42 @ X41)) = (X41))
% 0.83/1.06          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.83/1.06      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.83/1.06  thf('109', plain,
% 0.83/1.06      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['107', '108'])).
% 0.83/1.06  thf('110', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.06      inference('demod', [status(thm)], ['54', '58'])).
% 0.83/1.06  thf('111', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.83/1.06      inference('demod', [status(thm)], ['109', '110'])).
% 0.83/1.06  thf('112', plain, (![X38 : $i]: (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X38))),
% 0.83/1.06      inference('demod', [status(thm)], ['50', '51'])).
% 0.83/1.06  thf('113', plain,
% 0.83/1.06      (![X39 : $i, X40 : $i]:
% 0.83/1.06         ((m1_subset_1 @ (k3_subset_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39))
% 0.83/1.06          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.83/1.06  thf('114', plain,
% 0.83/1.06      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['112', '113'])).
% 0.83/1.06  thf('115', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.06      inference('demod', [status(thm)], ['54', '58'])).
% 0.83/1.06  thf('116', plain,
% 0.83/1.06      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.83/1.06      inference('demod', [status(thm)], ['114', '115'])).
% 0.83/1.06  thf('117', plain,
% 0.83/1.06      (![X36 : $i, X37 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.83/1.06          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.83/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.83/1.06  thf('118', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['116', '117'])).
% 0.83/1.06  thf('119', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['111', '118'])).
% 0.83/1.06  thf('120', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['111', '118'])).
% 0.83/1.06  thf('121', plain,
% 0.83/1.06      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('demod', [status(thm)], ['105', '106', '119', '120'])).
% 0.83/1.06  thf('122', plain,
% 0.83/1.06      ((m1_subset_1 @ 
% 0.83/1.06        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.06  thf('123', plain,
% 0.83/1.06      (![X41 : $i, X42 : $i]:
% 0.83/1.06         (((k3_subset_1 @ X42 @ (k3_subset_1 @ X42 @ X41)) = (X41))
% 0.83/1.06          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.83/1.06      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.83/1.06  thf('124', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.06         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.06          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.83/1.06         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['122', '123'])).
% 0.83/1.06  thf('125', plain,
% 0.83/1.06      (((k1_tops_1 @ sk_A @ sk_B)
% 0.83/1.06         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.06            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.83/1.06      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.83/1.06  thf('126', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.06         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.83/1.06      inference('demod', [status(thm)], ['124', '125'])).
% 0.83/1.06  thf('127', plain,
% 0.83/1.06      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.83/1.06          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('sup+', [status(thm)], ['121', '126'])).
% 0.83/1.06  thf('128', plain,
% 0.83/1.06      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('split', [status(esa)], ['4'])).
% 0.83/1.06  thf('129', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.83/1.06      inference('demod', [status(thm)], ['109', '110'])).
% 0.83/1.06  thf('130', plain,
% 0.83/1.06      ((((k2_struct_0 @ sk_A)
% 0.83/1.06          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.83/1.06  thf('131', plain,
% 0.83/1.06      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.83/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['33', '34'])).
% 0.83/1.06  thf('132', plain,
% 0.83/1.06      (![X51 : $i, X52 : $i]:
% 0.83/1.06         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.83/1.06          | ((k2_pre_topc @ X52 @ X51) != (k2_struct_0 @ X52))
% 0.83/1.06          | (v1_tops_1 @ X51 @ X52)
% 0.83/1.06          | ~ (l1_pre_topc @ X52))),
% 0.83/1.06      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.83/1.06  thf('133', plain,
% 0.83/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.06        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.83/1.06        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.83/1.06            != (k2_struct_0 @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['131', '132'])).
% 0.83/1.06  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('135', plain,
% 0.83/1.06      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.83/1.06        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.83/1.06            != (k2_struct_0 @ sk_A)))),
% 0.83/1.06      inference('demod', [status(thm)], ['133', '134'])).
% 0.83/1.06  thf('136', plain,
% 0.83/1.06      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.83/1.06         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('sup-', [status(thm)], ['130', '135'])).
% 0.83/1.06  thf('137', plain,
% 0.83/1.06      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('simplify', [status(thm)], ['136'])).
% 0.83/1.06  thf('138', plain,
% 0.83/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('139', plain,
% 0.83/1.06      (![X53 : $i, X54 : $i]:
% 0.83/1.06         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.83/1.06          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X54) @ X53) @ X54)
% 0.83/1.06          | (v2_tops_1 @ X53 @ X54)
% 0.83/1.06          | ~ (l1_pre_topc @ X54))),
% 0.83/1.06      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.83/1.06  thf('140', plain,
% 0.83/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.06        | (v2_tops_1 @ sk_B @ sk_A)
% 0.83/1.06        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.83/1.06      inference('sup-', [status(thm)], ['138', '139'])).
% 0.83/1.06  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('142', plain,
% 0.83/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.83/1.06         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.83/1.06      inference('demod', [status(thm)], ['20', '27'])).
% 0.83/1.06  thf('143', plain,
% 0.83/1.06      (((v2_tops_1 @ sk_B @ sk_A)
% 0.83/1.06        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.83/1.06      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.83/1.06  thf('144', plain,
% 0.83/1.06      (((v2_tops_1 @ sk_B @ sk_A))
% 0.83/1.06         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.83/1.06      inference('sup-', [status(thm)], ['137', '143'])).
% 0.83/1.06  thf('145', plain,
% 0.83/1.06      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.83/1.06      inference('split', [status(esa)], ['0'])).
% 0.83/1.06  thf('146', plain,
% 0.83/1.06      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.83/1.06       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.83/1.06      inference('sup-', [status(thm)], ['144', '145'])).
% 0.83/1.06  thf('147', plain, ($false),
% 0.83/1.06      inference('sat_resolution*', [status(thm)], ['1', '83', '84', '146'])).
% 0.83/1.06  
% 0.83/1.06  % SZS output end Refutation
% 0.83/1.06  
% 0.90/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
