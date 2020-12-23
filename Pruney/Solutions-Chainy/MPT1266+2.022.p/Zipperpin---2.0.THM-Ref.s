%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y8pxWlueLl

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:15 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  152 (1118 expanded)
%              Number of leaves         :   31 ( 364 expanded)
%              Depth                    :   18
%              Number of atoms          : 1249 (10590 expanded)
%              Number of equality atoms :   89 ( 754 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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

thf('2',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('9',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('11',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_subset_1 @ X7 @ X8 @ ( k3_subset_1 @ X7 @ X8 ) )
        = ( k2_subset_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_subset_1 @ X7 @ X8 @ ( k3_subset_1 @ X7 @ X8 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('22',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_subset_1 @ X7 @ X8 @ ( k3_subset_1 @ X7 @ X8 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','40','45'])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tops_1 @ X22 @ X23 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v2_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','48'])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('53',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','23'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','40','45'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('73',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['63','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('76',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('82',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('83',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_pre_topc @ X21 @ X20 )
       != ( k2_struct_0 @ X21 ) )
      | ( v1_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('89',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('91',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('92',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('99',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('101',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','101'])).

thf('103',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('105',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','23'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','40','45'])).

thf('109',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ( v2_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ X1 @ X0 )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','15','22'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('115',plain,
    ( ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','115'])).

thf('117',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','79','80','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y8pxWlueLl
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:36:12 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.60/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.79  % Solved by: fo/fo7.sh
% 0.60/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.79  % done 1090 iterations in 0.390s
% 0.60/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.79  % SZS output start Refutation
% 0.60/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.60/0.79  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.60/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.79  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.60/0.79  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.60/0.79  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.60/0.79  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.60/0.79  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.60/0.79  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.60/0.79  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.60/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.79  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.60/0.79  thf(t84_tops_1, conjecture,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_pre_topc @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79           ( ( v2_tops_1 @ B @ A ) <=>
% 0.60/0.79             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.79    (~( ![A:$i]:
% 0.60/0.79        ( ( l1_pre_topc @ A ) =>
% 0.60/0.79          ( ![B:$i]:
% 0.60/0.79            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79              ( ( v2_tops_1 @ B @ A ) <=>
% 0.60/0.79                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.60/0.79    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.60/0.79  thf('0', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.60/0.79        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('1', plain,
% 0.60/0.79      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.60/0.79       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('split', [status(esa)], ['0'])).
% 0.60/0.79  thf('2', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('3', plain,
% 0.60/0.79      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['2'])).
% 0.60/0.79  thf('4', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('5', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(dt_k3_subset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.79       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.60/0.79  thf('6', plain,
% 0.60/0.79      (![X2 : $i, X3 : $i]:
% 0.60/0.79         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.60/0.79          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.60/0.79  thf('7', plain,
% 0.60/0.79      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf(t18_pre_topc, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_struct_0 @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79           ( ( k4_subset_1 @
% 0.60/0.79               ( u1_struct_0 @ A ) @ B @ 
% 0.60/0.79               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.60/0.79             ( k2_struct_0 @ A ) ) ) ) ))).
% 0.60/0.79  thf('8', plain,
% 0.60/0.79      (![X16 : $i, X17 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.60/0.79          | ((k4_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.60/0.79              (k3_subset_1 @ (u1_struct_0 @ X17) @ X16)) = (k2_struct_0 @ X17))
% 0.60/0.79          | ~ (l1_struct_0 @ X17))),
% 0.60/0.79      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.60/0.79  thf('9', plain,
% 0.60/0.79      ((~ (l1_struct_0 @ sk_A)
% 0.60/0.79        | ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.60/0.79            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.60/0.79            = (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.79  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(dt_l1_pre_topc, axiom,
% 0.60/0.79    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.60/0.79  thf('11', plain,
% 0.60/0.79      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.60/0.79  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.79  thf('13', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(involutiveness_k3_subset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.79       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.60/0.79  thf('14', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.60/0.79          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.60/0.79      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.60/0.79  thf('15', plain,
% 0.60/0.79      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.79  thf('16', plain,
% 0.60/0.79      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf(t25_subset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.79       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.60/0.79         ( k2_subset_1 @ A ) ) ))).
% 0.60/0.79  thf('17', plain,
% 0.60/0.79      (![X7 : $i, X8 : $i]:
% 0.60/0.79         (((k4_subset_1 @ X7 @ X8 @ (k3_subset_1 @ X7 @ X8))
% 0.60/0.79            = (k2_subset_1 @ X7))
% 0.60/0.79          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.60/0.79  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.60/0.79  thf('18', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.60/0.79      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.60/0.79  thf('19', plain,
% 0.60/0.79      (![X7 : $i, X8 : $i]:
% 0.60/0.79         (((k4_subset_1 @ X7 @ X8 @ (k3_subset_1 @ X7 @ X8)) = (X7))
% 0.60/0.79          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.60/0.79      inference('demod', [status(thm)], ['17', '18'])).
% 0.60/0.79  thf('20', plain,
% 0.60/0.79      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.60/0.79         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.60/0.79         = (u1_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['16', '19'])).
% 0.60/0.79  thf('21', plain,
% 0.60/0.79      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.79  thf('22', plain,
% 0.60/0.79      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.60/0.79         = (u1_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['20', '21'])).
% 0.60/0.79  thf('23', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('24', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['4', '23'])).
% 0.60/0.79  thf(t4_subset_1, axiom,
% 0.60/0.79    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.79  thf('25', plain,
% 0.60/0.79      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.60/0.79      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.79  thf('26', plain,
% 0.60/0.79      (![X2 : $i, X3 : $i]:
% 0.60/0.79         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.60/0.79          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.60/0.79  thf('27', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.60/0.79  thf('28', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.60/0.79      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.60/0.79  thf(t22_subset_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.60/0.79  thf('29', plain,
% 0.60/0.79      (![X6 : $i]:
% 0.60/0.79         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.60/0.79  thf('30', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.60/0.79      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.60/0.79  thf('31', plain,
% 0.60/0.79      (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.60/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.60/0.79  thf('32', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.60/0.79      inference('sup+', [status(thm)], ['28', '31'])).
% 0.60/0.79  thf('33', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.60/0.79      inference('demod', [status(thm)], ['27', '32'])).
% 0.60/0.79  thf('34', plain,
% 0.60/0.79      (![X16 : $i, X17 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.60/0.79          | ((k4_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.60/0.79              (k3_subset_1 @ (u1_struct_0 @ X17) @ X16)) = (k2_struct_0 @ X17))
% 0.60/0.79          | ~ (l1_struct_0 @ X17))),
% 0.60/0.79      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.60/0.79  thf('35', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_struct_0 @ X0)
% 0.60/0.79          | ((k4_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.60/0.79              (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.60/0.79              = (k2_struct_0 @ X0)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.79  thf('36', plain,
% 0.60/0.79      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.60/0.79      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.79  thf('37', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.60/0.79          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.60/0.79      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.60/0.79  thf('38', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.79  thf('39', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.60/0.79      inference('sup+', [status(thm)], ['28', '31'])).
% 0.60/0.79  thf('40', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.79      inference('demod', [status(thm)], ['38', '39'])).
% 0.60/0.79  thf('41', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.60/0.79      inference('demod', [status(thm)], ['27', '32'])).
% 0.60/0.79  thf('42', plain,
% 0.60/0.79      (![X7 : $i, X8 : $i]:
% 0.60/0.79         (((k4_subset_1 @ X7 @ X8 @ (k3_subset_1 @ X7 @ X8)) = (X7))
% 0.60/0.79          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.60/0.79      inference('demod', [status(thm)], ['17', '18'])).
% 0.60/0.79  thf('43', plain,
% 0.60/0.79      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['41', '42'])).
% 0.60/0.79  thf('44', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.79      inference('demod', [status(thm)], ['38', '39'])).
% 0.60/0.79  thf('45', plain,
% 0.60/0.79      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.60/0.79  thf('46', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.60/0.79      inference('demod', [status(thm)], ['35', '40', '45'])).
% 0.60/0.79  thf(d4_tops_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_pre_topc @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79           ( ( v2_tops_1 @ B @ A ) <=>
% 0.60/0.79             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.60/0.79  thf('47', plain,
% 0.60/0.79      (![X22 : $i, X23 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.60/0.79          | ~ (v2_tops_1 @ X22 @ X23)
% 0.60/0.79          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.60/0.79          | ~ (l1_pre_topc @ X23))),
% 0.60/0.79      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.60/0.79  thf('48', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.60/0.79          | ~ (v2_tops_1 @ X1 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.60/0.79  thf('49', plain,
% 0.60/0.79      ((~ (v2_tops_1 @ sk_B @ sk_A)
% 0.60/0.79        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['24', '48'])).
% 0.60/0.79  thf('50', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.79  thf('53', plain,
% 0.60/0.79      ((~ (v2_tops_1 @ sk_B @ sk_A)
% 0.60/0.79        | (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.60/0.79  thf('54', plain,
% 0.60/0.79      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.60/0.79         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['3', '53'])).
% 0.60/0.79  thf('55', plain,
% 0.60/0.79      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf(d3_tops_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_pre_topc @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79           ( ( v1_tops_1 @ B @ A ) <=>
% 0.60/0.79             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.60/0.79  thf('56', plain,
% 0.60/0.79      (![X20 : $i, X21 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.60/0.79          | ~ (v1_tops_1 @ X20 @ X21)
% 0.60/0.79          | ((k2_pre_topc @ X21 @ X20) = (k2_struct_0 @ X21))
% 0.60/0.79          | ~ (l1_pre_topc @ X21))),
% 0.60/0.79      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.60/0.79  thf('57', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.60/0.79            = (k2_struct_0 @ sk_A))
% 0.60/0.79        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['55', '56'])).
% 0.60/0.79  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('59', plain,
% 0.60/0.79      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.60/0.79          = (k2_struct_0 @ sk_A))
% 0.60/0.79        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['57', '58'])).
% 0.60/0.79  thf('60', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('61', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('62', plain,
% 0.60/0.79      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.60/0.79          = (k2_struct_0 @ sk_A))
% 0.60/0.79        | ~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.60/0.79  thf('63', plain,
% 0.60/0.79      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.60/0.79          = (k2_struct_0 @ sk_A)))
% 0.60/0.79         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['54', '62'])).
% 0.60/0.79  thf('64', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['4', '23'])).
% 0.60/0.79  thf('65', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.60/0.79      inference('demod', [status(thm)], ['35', '40', '45'])).
% 0.60/0.79  thf(d1_tops_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_pre_topc @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79           ( ( k1_tops_1 @ A @ B ) =
% 0.60/0.79             ( k3_subset_1 @
% 0.60/0.79               ( u1_struct_0 @ A ) @ 
% 0.60/0.79               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.60/0.79  thf('66', plain,
% 0.60/0.79      (![X18 : $i, X19 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.60/0.79          | ((k1_tops_1 @ X19 @ X18)
% 0.60/0.79              = (k3_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.60/0.79                 (k2_pre_topc @ X19 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18))))
% 0.60/0.79          | ~ (l1_pre_topc @ X19))),
% 0.60/0.79      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.60/0.79  thf('67', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ((k1_tops_1 @ X0 @ X1)
% 0.60/0.79              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.60/0.79                 (k2_pre_topc @ X0 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['65', '66'])).
% 0.60/0.79  thf('68', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.79          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['64', '67'])).
% 0.60/0.79  thf('69', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('70', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.79  thf('73', plain,
% 0.60/0.79      (((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.79         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.60/0.79            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.60/0.79      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.60/0.79  thf('74', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.79          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.60/0.79         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['63', '73'])).
% 0.60/0.79  thf('75', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.79      inference('demod', [status(thm)], ['38', '39'])).
% 0.60/0.79  thf('76', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.60/0.79         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['74', '75'])).
% 0.60/0.79  thf('77', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.60/0.79         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.79      inference('split', [status(esa)], ['0'])).
% 0.60/0.79  thf('78', plain,
% 0.60/0.79      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.60/0.79         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.60/0.79             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['76', '77'])).
% 0.60/0.79  thf('79', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.60/0.79       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('simplify', [status(thm)], ['78'])).
% 0.60/0.79  thf('80', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.60/0.79       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('split', [status(esa)], ['2'])).
% 0.60/0.79  thf('81', plain,
% 0.60/0.79      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.60/0.79         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.79      inference('split', [status(esa)], ['2'])).
% 0.60/0.79  thf('82', plain,
% 0.60/0.79      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf('83', plain,
% 0.60/0.79      (![X20 : $i, X21 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.60/0.79          | ((k2_pre_topc @ X21 @ X20) != (k2_struct_0 @ X21))
% 0.60/0.79          | (v1_tops_1 @ X20 @ X21)
% 0.60/0.79          | ~ (l1_pre_topc @ X21))),
% 0.60/0.79      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.60/0.79  thf('84', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.79        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.60/0.79            != (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['82', '83'])).
% 0.60/0.79  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('86', plain,
% 0.60/0.79      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.79        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.60/0.79            != (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['84', '85'])).
% 0.60/0.79  thf('87', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('88', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('89', plain,
% 0.60/0.79      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.79        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.60/0.79            != (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.60/0.79  thf('90', plain,
% 0.60/0.79      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf(dt_k2_pre_topc, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( l1_pre_topc @ A ) & 
% 0.60/0.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.79       ( m1_subset_1 @
% 0.60/0.79         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.79  thf('91', plain,
% 0.60/0.79      (![X13 : $i, X14 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X13)
% 0.60/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.60/0.79          | (m1_subset_1 @ (k2_pre_topc @ X13 @ X14) @ 
% 0.60/0.79             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.60/0.79  thf('92', plain,
% 0.60/0.79      (((m1_subset_1 @ 
% 0.60/0.79         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.60/0.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['90', '91'])).
% 0.60/0.79  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('94', plain,
% 0.60/0.79      ((m1_subset_1 @ 
% 0.60/0.79        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['92', '93'])).
% 0.60/0.79  thf('95', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('96', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('97', plain,
% 0.60/0.79      ((m1_subset_1 @ 
% 0.60/0.79        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.60/0.79  thf('98', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.60/0.79          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.60/0.79      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.60/0.79  thf('99', plain,
% 0.60/0.79      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.60/0.79         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.60/0.79          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.60/0.79         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['97', '98'])).
% 0.60/0.79  thf('100', plain,
% 0.60/0.79      (((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.79         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.60/0.79            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.60/0.79      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.60/0.79  thf('101', plain,
% 0.60/0.79      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.60/0.79         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.60/0.79      inference('demod', [status(thm)], ['99', '100'])).
% 0.60/0.79  thf('102', plain,
% 0.60/0.79      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.79        | ((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.60/0.79            != (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['89', '101'])).
% 0.60/0.79  thf('103', plain,
% 0.60/0.79      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.60/0.79           != (k2_struct_0 @ sk_A))
% 0.60/0.79         | (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.60/0.79         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['81', '102'])).
% 0.60/0.79  thf('104', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.60/0.79      inference('sup+', [status(thm)], ['28', '31'])).
% 0.60/0.79  thf('105', plain,
% 0.60/0.79      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.60/0.79         | (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.60/0.79         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.79      inference('demod', [status(thm)], ['103', '104'])).
% 0.60/0.79  thf('106', plain,
% 0.60/0.79      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.60/0.79         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.79      inference('simplify', [status(thm)], ['105'])).
% 0.60/0.79  thf('107', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['4', '23'])).
% 0.60/0.79  thf('108', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.60/0.79      inference('demod', [status(thm)], ['35', '40', '45'])).
% 0.60/0.79  thf('109', plain,
% 0.60/0.79      (![X22 : $i, X23 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.60/0.79          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.60/0.79          | (v2_tops_1 @ X22 @ X23)
% 0.60/0.79          | ~ (l1_pre_topc @ X23))),
% 0.60/0.79      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.60/0.79  thf('110', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | (v2_tops_1 @ X1 @ X0)
% 0.60/0.79          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['108', '109'])).
% 0.60/0.79  thf('111', plain,
% 0.60/0.79      ((~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.79        | (v2_tops_1 @ sk_B @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['107', '110'])).
% 0.60/0.79  thf('112', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['9', '12', '15', '22'])).
% 0.60/0.79  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.79  thf('115', plain,
% 0.60/0.79      ((~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.79        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.60/0.79  thf('116', plain,
% 0.60/0.79      (((v2_tops_1 @ sk_B @ sk_A))
% 0.60/0.79         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['106', '115'])).
% 0.60/0.79  thf('117', plain,
% 0.60/0.79      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['0'])).
% 0.60/0.79  thf('118', plain,
% 0.60/0.79      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.60/0.79       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['116', '117'])).
% 0.60/0.79  thf('119', plain, ($false),
% 0.60/0.79      inference('sat_resolution*', [status(thm)], ['1', '79', '80', '118'])).
% 0.60/0.79  
% 0.60/0.79  % SZS output end Refutation
% 0.60/0.79  
% 0.60/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
