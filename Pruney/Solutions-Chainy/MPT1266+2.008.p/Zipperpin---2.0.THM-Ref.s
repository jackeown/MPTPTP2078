%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NQLTziW147

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:13 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  188 (1225 expanded)
%              Number of leaves         :   34 ( 378 expanded)
%              Depth                    :   24
%              Number of atoms          : 1569 (11244 expanded)
%              Number of equality atoms :  121 ( 746 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tops_1 @ X24 @ X25 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
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
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('34',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('38',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v1_tops_1 @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k2_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('51',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['3','51'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['53'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('57',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('58',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('59',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('63',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('69',plain,(
    ! [X6: $i] :
      ( ( k1_subset_1 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('70',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = ( k3_subset_1 @ X15 @ ( k1_subset_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('71',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('72',plain,(
    ! [X15: $i] :
      ( X15
      = ( k3_subset_1 @ X15 @ ( k1_subset_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('76',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','74','75'])).

thf('77',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('78',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','81'])).

thf('83',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('85',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X21 @ X20 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('91',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['85','91'])).

thf('93',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('100',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('102',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('103',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('105',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('106',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','106'])).

thf('108',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('109',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('110',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','110'])).

thf('112',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('114',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('116',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','120'])).

thf('122',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('123',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('125',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('127',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('129',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['124','129'])).

thf('131',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('132',plain,
    ( ( k1_xboole_0
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('134',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','132','133'])).

thf('135',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('137',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_pre_topc @ X23 @ X22 )
       != ( k2_struct_0 @ X23 ) )
      | ( v1_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('138',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','140'])).

thf('142',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ( v2_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('148',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['142','148'])).

thf('150',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('151',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','98','99','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NQLTziW147
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 959 iterations in 0.274s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.51/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.51/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.51/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.73  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.51/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.73  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.51/0.73  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.51/0.73  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.51/0.73  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.51/0.73  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.51/0.73  thf(t84_tops_1, conjecture,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( l1_pre_topc @ A ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73           ( ( v2_tops_1 @ B @ A ) <=>
% 0.51/0.73             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.73    (~( ![A:$i]:
% 0.51/0.73        ( ( l1_pre_topc @ A ) =>
% 0.51/0.73          ( ![B:$i]:
% 0.51/0.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73              ( ( v2_tops_1 @ B @ A ) <=>
% 0.51/0.73                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.51/0.73  thf('0', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.51/0.73        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.51/0.73       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf(d3_struct_0, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.51/0.73  thf('2', plain,
% 0.51/0.73      (![X16 : $i]:
% 0.51/0.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.73  thf('3', plain,
% 0.51/0.73      (![X16 : $i]:
% 0.51/0.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.73  thf('4', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('5', plain,
% 0.51/0.73      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('split', [status(esa)], ['4'])).
% 0.51/0.73  thf('6', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(d4_tops_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( l1_pre_topc @ A ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73           ( ( v2_tops_1 @ B @ A ) <=>
% 0.51/0.73             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.51/0.73  thf('7', plain,
% 0.51/0.73      (![X24 : $i, X25 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.51/0.73          | ~ (v2_tops_1 @ X24 @ X25)
% 0.51/0.73          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 0.51/0.73          | ~ (l1_pre_topc @ X25))),
% 0.51/0.73      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.51/0.73  thf('8', plain,
% 0.51/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.51/0.73        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.51/0.73  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('10', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(d5_subset_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.73       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.51/0.73          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.73  thf('12', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.73  thf('13', plain,
% 0.51/0.73      (![X16 : $i]:
% 0.51/0.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.73  thf('14', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.73  thf('15', plain,
% 0.51/0.73      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.51/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.73      inference('sup+', [status(thm)], ['13', '14'])).
% 0.51/0.73  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(dt_l1_pre_topc, axiom,
% 0.51/0.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.51/0.73  thf('17', plain,
% 0.51/0.73      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.51/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.51/0.73  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('19', plain,
% 0.51/0.73      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('demod', [status(thm)], ['15', '18'])).
% 0.51/0.73  thf('20', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('demod', [status(thm)], ['12', '19'])).
% 0.51/0.73  thf('21', plain,
% 0.51/0.73      (![X16 : $i]:
% 0.51/0.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.73  thf('22', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('23', plain,
% 0.51/0.73      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.73      inference('sup+', [status(thm)], ['21', '22'])).
% 0.51/0.73  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('25', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['23', '24'])).
% 0.51/0.73  thf('26', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.51/0.73          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.73  thf('27', plain,
% 0.51/0.73      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('demod', [status(thm)], ['20', '27'])).
% 0.51/0.73  thf('29', plain,
% 0.51/0.73      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.51/0.73        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['8', '9', '28'])).
% 0.51/0.73  thf('30', plain,
% 0.51/0.73      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['5', '29'])).
% 0.51/0.73  thf('31', plain,
% 0.51/0.73      (![X16 : $i]:
% 0.51/0.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.73  thf('32', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(dt_k3_subset_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.73       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.73  thf('33', plain,
% 0.51/0.73      (![X11 : $i, X12 : $i]:
% 0.51/0.73         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.51/0.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.51/0.73      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.51/0.73  thf('34', plain,
% 0.51/0.73      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['32', '33'])).
% 0.51/0.73  thf('35', plain,
% 0.51/0.73      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.51/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.73      inference('sup+', [status(thm)], ['31', '34'])).
% 0.51/0.73  thf('36', plain,
% 0.51/0.73      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.73  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('38', plain,
% 0.51/0.73      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.51/0.73  thf(d3_tops_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( l1_pre_topc @ A ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73           ( ( v1_tops_1 @ B @ A ) <=>
% 0.51/0.73             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.51/0.73  thf('39', plain,
% 0.51/0.73      (![X22 : $i, X23 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.51/0.73          | ~ (v1_tops_1 @ X22 @ X23)
% 0.51/0.73          | ((k2_pre_topc @ X23 @ X22) = (k2_struct_0 @ X23))
% 0.51/0.73          | ~ (l1_pre_topc @ X23))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.51/0.73  thf('40', plain,
% 0.51/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.51/0.73            = (k2_struct_0 @ sk_A))
% 0.51/0.73        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['38', '39'])).
% 0.51/0.73  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('42', plain,
% 0.51/0.73      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.51/0.73          = (k2_struct_0 @ sk_A))
% 0.51/0.73        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.73  thf('43', plain,
% 0.51/0.73      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.51/0.73          = (k2_struct_0 @ sk_A)))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['30', '42'])).
% 0.51/0.73  thf('44', plain,
% 0.51/0.73      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.51/0.73  thf(dt_k2_pre_topc, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ( l1_pre_topc @ A ) & 
% 0.51/0.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.73       ( m1_subset_1 @
% 0.51/0.73         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.73  thf('45', plain,
% 0.51/0.73      (![X17 : $i, X18 : $i]:
% 0.51/0.73         (~ (l1_pre_topc @ X17)
% 0.51/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.73          | (m1_subset_1 @ (k2_pre_topc @ X17 @ X18) @ 
% 0.51/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.51/0.73      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.51/0.73  thf('46', plain,
% 0.51/0.73      (((m1_subset_1 @ 
% 0.51/0.73         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.51/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.51/0.73  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('48', plain,
% 0.51/0.73      ((m1_subset_1 @ 
% 0.51/0.73        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['46', '47'])).
% 0.51/0.73  thf('49', plain,
% 0.51/0.73      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.51/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['43', '48'])).
% 0.51/0.73  thf('50', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.51/0.73          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.73  thf('51', plain,
% 0.51/0.73      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.51/0.73          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['49', '50'])).
% 0.51/0.73  thf('52', plain,
% 0.51/0.73      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.51/0.73           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.51/0.73         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['3', '51'])).
% 0.51/0.73  thf(d10_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.73  thf('53', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.73  thf('54', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.73      inference('simplify', [status(thm)], ['53'])).
% 0.51/0.73  thf(l32_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.73  thf('55', plain,
% 0.51/0.73      (![X3 : $i, X5 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.51/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.73  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['54', '55'])).
% 0.51/0.73  thf(dt_k2_subset_1, axiom,
% 0.51/0.73    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.51/0.73  thf('57', plain,
% 0.51/0.73      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.51/0.73      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.51/0.73  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.51/0.73  thf('58', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.51/0.73      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.51/0.73  thf('59', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.51/0.73      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.73  thf('60', plain,
% 0.51/0.73      (![X11 : $i, X12 : $i]:
% 0.51/0.73         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.51/0.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.51/0.73      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.51/0.73  thf('61', plain,
% 0.51/0.73      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['59', '60'])).
% 0.51/0.73  thf('62', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.51/0.73      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.73  thf('63', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.51/0.73          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.73  thf('64', plain,
% 0.51/0.73      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['62', '63'])).
% 0.51/0.73  thf('65', plain,
% 0.51/0.73      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.51/0.73      inference('demod', [status(thm)], ['61', '64'])).
% 0.51/0.73  thf('66', plain,
% 0.51/0.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['56', '65'])).
% 0.51/0.73  thf(involutiveness_k3_subset_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.73       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.51/0.73  thf('67', plain,
% 0.51/0.73      (![X13 : $i, X14 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.51/0.73          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.51/0.73      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.51/0.73  thf('68', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.51/0.73  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.51/0.73  thf('69', plain, (![X6 : $i]: ((k1_subset_1 @ X6) = (k1_xboole_0))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.51/0.73  thf(t22_subset_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.51/0.73  thf('70', plain,
% 0.51/0.73      (![X15 : $i]:
% 0.51/0.73         ((k2_subset_1 @ X15) = (k3_subset_1 @ X15 @ (k1_subset_1 @ X15)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.51/0.73  thf('71', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.51/0.73      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.51/0.73  thf('72', plain,
% 0.51/0.73      (![X15 : $i]: ((X15) = (k3_subset_1 @ X15 @ (k1_subset_1 @ X15)))),
% 0.51/0.73      inference('demod', [status(thm)], ['70', '71'])).
% 0.51/0.73  thf('73', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['69', '72'])).
% 0.51/0.73  thf('74', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.73      inference('demod', [status(thm)], ['68', '73'])).
% 0.51/0.73  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('76', plain,
% 0.51/0.73      ((((k1_xboole_0)
% 0.51/0.73          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['52', '74', '75'])).
% 0.51/0.73  thf('77', plain,
% 0.51/0.73      (![X3 : $i, X4 : $i]:
% 0.51/0.73         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.51/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.73  thf('78', plain,
% 0.51/0.73      (((((k1_xboole_0) != (k1_xboole_0))
% 0.51/0.73         | (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['76', '77'])).
% 0.51/0.73  thf('79', plain,
% 0.51/0.73      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('simplify', [status(thm)], ['78'])).
% 0.51/0.73  thf('80', plain,
% 0.51/0.73      (![X0 : $i, X2 : $i]:
% 0.51/0.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.51/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.73  thf('81', plain,
% 0.51/0.73      (((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.73         | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['79', '80'])).
% 0.51/0.73  thf('82', plain,
% 0.51/0.73      (((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.51/0.73         | ~ (l1_struct_0 @ sk_A)
% 0.51/0.73         | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['2', '81'])).
% 0.51/0.73  thf('83', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.73      inference('simplify', [status(thm)], ['53'])).
% 0.51/0.73  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('85', plain,
% 0.51/0.73      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.51/0.73  thf('86', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(d1_tops_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( l1_pre_topc @ A ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73           ( ( k1_tops_1 @ A @ B ) =
% 0.51/0.73             ( k3_subset_1 @
% 0.51/0.73               ( u1_struct_0 @ A ) @ 
% 0.51/0.73               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.51/0.73  thf('87', plain,
% 0.51/0.73      (![X20 : $i, X21 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.51/0.73          | ((k1_tops_1 @ X21 @ X20)
% 0.51/0.73              = (k3_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.51/0.73                 (k2_pre_topc @ X21 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20))))
% 0.51/0.73          | ~ (l1_pre_topc @ X21))),
% 0.51/0.73      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.51/0.73  thf('88', plain,
% 0.51/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73               (k2_pre_topc @ sk_A @ 
% 0.51/0.73                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['86', '87'])).
% 0.51/0.73  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('90', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('demod', [status(thm)], ['20', '27'])).
% 0.51/0.73  thf('91', plain,
% 0.51/0.73      (((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.51/0.73      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.51/0.73  thf('92', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.51/0.73             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['85', '91'])).
% 0.51/0.73  thf('93', plain,
% 0.51/0.73      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.51/0.73          = (k2_struct_0 @ sk_A)))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['30', '42'])).
% 0.51/0.73  thf('94', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.73      inference('demod', [status(thm)], ['68', '73'])).
% 0.51/0.73  thf('95', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.51/0.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.51/0.73  thf('96', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.51/0.73         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf('97', plain,
% 0.51/0.73      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.51/0.73         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.51/0.73             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['95', '96'])).
% 0.51/0.73  thf('98', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.51/0.73       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.73      inference('simplify', [status(thm)], ['97'])).
% 0.51/0.73  thf('99', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.51/0.73       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.73      inference('split', [status(esa)], ['4'])).
% 0.51/0.73  thf('100', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('split', [status(esa)], ['4'])).
% 0.51/0.73  thf('101', plain,
% 0.51/0.73      ((m1_subset_1 @ 
% 0.51/0.73        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['46', '47'])).
% 0.51/0.73  thf('102', plain,
% 0.51/0.73      (![X13 : $i, X14 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.51/0.73          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.51/0.73      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.51/0.73  thf('103', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.51/0.73         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['101', '102'])).
% 0.51/0.73  thf('104', plain,
% 0.51/0.73      ((m1_subset_1 @ 
% 0.51/0.73        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['46', '47'])).
% 0.51/0.73  thf('105', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.51/0.73          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.73  thf('106', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.51/0.73         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['104', '105'])).
% 0.51/0.73  thf('107', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.51/0.73         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.51/0.73      inference('demod', [status(thm)], ['103', '106'])).
% 0.51/0.73  thf('108', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.51/0.73         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['104', '105'])).
% 0.51/0.73  thf('109', plain,
% 0.51/0.73      (((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.51/0.73      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.51/0.73  thf('110', plain,
% 0.51/0.73      (((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.51/0.73      inference('sup+', [status(thm)], ['108', '109'])).
% 0.51/0.73  thf('111', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.51/0.73         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.51/0.73      inference('demod', [status(thm)], ['107', '110'])).
% 0.51/0.73  thf('112', plain,
% 0.51/0.73      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.51/0.73          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('sup+', [status(thm)], ['100', '111'])).
% 0.51/0.73  thf('113', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['69', '72'])).
% 0.51/0.73  thf('114', plain,
% 0.51/0.73      ((((u1_struct_0 @ sk_A)
% 0.51/0.73          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('demod', [status(thm)], ['112', '113'])).
% 0.51/0.73  thf('115', plain,
% 0.51/0.73      ((((u1_struct_0 @ sk_A)
% 0.51/0.73          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('demod', [status(thm)], ['112', '113'])).
% 0.51/0.73  thf('116', plain,
% 0.51/0.73      (![X16 : $i]:
% 0.51/0.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.73  thf('117', plain,
% 0.51/0.73      ((m1_subset_1 @ 
% 0.51/0.73        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['46', '47'])).
% 0.51/0.73  thf('118', plain,
% 0.51/0.73      (((m1_subset_1 @ 
% 0.51/0.73         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.51/0.73         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.73      inference('sup+', [status(thm)], ['116', '117'])).
% 0.51/0.73  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('120', plain,
% 0.51/0.73      ((m1_subset_1 @ 
% 0.51/0.73        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['118', '119'])).
% 0.51/0.73  thf('121', plain,
% 0.51/0.73      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('sup+', [status(thm)], ['115', '120'])).
% 0.51/0.73  thf('122', plain,
% 0.51/0.73      (![X13 : $i, X14 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.51/0.73          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.51/0.73      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.51/0.73  thf('123', plain,
% 0.51/0.73      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.51/0.73          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.51/0.73          = (u1_struct_0 @ sk_A)))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['121', '122'])).
% 0.51/0.73  thf('124', plain,
% 0.51/0.73      ((((u1_struct_0 @ sk_A)
% 0.51/0.73          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('demod', [status(thm)], ['112', '113'])).
% 0.51/0.73  thf('125', plain,
% 0.51/0.73      (![X16 : $i]:
% 0.51/0.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.73  thf('126', plain,
% 0.51/0.73      (((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.73            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.51/0.73      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.51/0.73  thf('127', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.51/0.73             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.51/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.73      inference('sup+', [status(thm)], ['125', '126'])).
% 0.51/0.73  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('129', plain,
% 0.51/0.73      (((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.51/0.73            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.51/0.73      inference('demod', [status(thm)], ['127', '128'])).
% 0.51/0.73  thf('130', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.51/0.73          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('sup+', [status(thm)], ['124', '129'])).
% 0.51/0.73  thf('131', plain,
% 0.51/0.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('split', [status(esa)], ['4'])).
% 0.51/0.73  thf('132', plain,
% 0.51/0.73      ((((k1_xboole_0)
% 0.51/0.73          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('demod', [status(thm)], ['130', '131'])).
% 0.51/0.73  thf('133', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['69', '72'])).
% 0.51/0.73  thf('134', plain,
% 0.51/0.73      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('demod', [status(thm)], ['123', '132', '133'])).
% 0.51/0.73  thf('135', plain,
% 0.51/0.73      ((((k2_struct_0 @ sk_A)
% 0.51/0.73          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('demod', [status(thm)], ['114', '134'])).
% 0.51/0.73  thf('136', plain,
% 0.51/0.73      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.51/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.51/0.73  thf('137', plain,
% 0.51/0.73      (![X22 : $i, X23 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.51/0.73          | ((k2_pre_topc @ X23 @ X22) != (k2_struct_0 @ X23))
% 0.51/0.73          | (v1_tops_1 @ X22 @ X23)
% 0.51/0.73          | ~ (l1_pre_topc @ X23))),
% 0.51/0.73      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.51/0.73  thf('138', plain,
% 0.51/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.51/0.73        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.51/0.73            != (k2_struct_0 @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['136', '137'])).
% 0.51/0.73  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('140', plain,
% 0.51/0.73      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.51/0.73        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.51/0.73            != (k2_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['138', '139'])).
% 0.51/0.73  thf('141', plain,
% 0.51/0.73      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.51/0.73         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['135', '140'])).
% 0.51/0.73  thf('142', plain,
% 0.51/0.73      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('simplify', [status(thm)], ['141'])).
% 0.51/0.73  thf('143', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('144', plain,
% 0.51/0.73      (![X24 : $i, X25 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.51/0.73          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 0.51/0.73          | (v2_tops_1 @ X24 @ X25)
% 0.51/0.73          | ~ (l1_pre_topc @ X25))),
% 0.51/0.73      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.51/0.73  thf('145', plain,
% 0.51/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v2_tops_1 @ sk_B @ sk_A)
% 0.51/0.73        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['143', '144'])).
% 0.51/0.73  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('147', plain,
% 0.51/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.51/0.73         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.51/0.73      inference('demod', [status(thm)], ['20', '27'])).
% 0.51/0.73  thf('148', plain,
% 0.51/0.73      (((v2_tops_1 @ sk_B @ sk_A)
% 0.51/0.73        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.51/0.73  thf('149', plain,
% 0.51/0.73      (((v2_tops_1 @ sk_B @ sk_A))
% 0.51/0.73         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['142', '148'])).
% 0.51/0.73  thf('150', plain,
% 0.51/0.73      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf('151', plain,
% 0.51/0.73      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.51/0.73       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['149', '150'])).
% 0.51/0.73  thf('152', plain, ($false),
% 0.51/0.73      inference('sat_resolution*', [status(thm)], ['1', '98', '99', '151'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
