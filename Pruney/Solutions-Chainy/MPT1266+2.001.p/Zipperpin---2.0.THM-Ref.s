%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d1bqVz76WL

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:11 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  202 (1580 expanded)
%              Number of leaves         :   42 ( 491 expanded)
%              Depth                    :   27
%              Number of atoms          : 1694 (14386 expanded)
%              Number of equality atoms :  114 ( 981 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X69 ) ) )
      | ~ ( v2_tops_1 @ X68 @ X69 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X69 ) @ X68 ) @ X69 )
      | ~ ( l1_pre_topc @ X69 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X59: $i] :
      ( ( l1_struct_0 @ X59 )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('24',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('27',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','26'])).

thf('28',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('33',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ~ ( v1_tops_1 @ X66 @ X67 )
      | ( ( k2_pre_topc @ X67 @ X66 )
        = ( k2_struct_0 @ X67 ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ( ( k1_tops_1 @ X65 @ X64 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X65 ) @ ( k2_pre_topc @ X65 @ ( k3_subset_1 @ ( u1_struct_0 @ X65 ) @ X64 ) ) ) )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('48',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','48'])).

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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X47: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('57',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X45 @ X44 ) @ X46 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X45 @ X46 ) @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X47: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('63',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('65',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('72',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','73'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','74','76'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('78',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','81'])).

thf('83',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('87',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('88',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('90',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X42 @ X41 ) @ ( k3_subset_1 @ X42 @ X43 ) )
      | ( r1_tarski @ X43 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('96',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X57 @ X58 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95','100'])).

thf('102',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','101'])).

thf('103',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('104',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('108',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('113',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('115',plain,
    ( ( k1_xboole_0
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X47: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('117',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X45 @ X44 ) @ X46 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X45 @ X46 ) @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','73'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('123',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('124',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('126',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('128',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['123','128'])).

thf('130',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122','129'])).

thf('131',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('132',plain,
    ( ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('134',plain,(
    ! [X56: $i] :
      ( ( ( k2_struct_0 @ X56 )
        = ( u1_struct_0 @ X56 ) )
      | ~ ( l1_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('136',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('138',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['133','138'])).

thf('140',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','139'])).

thf('141',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('143',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( ( k2_pre_topc @ X67 @ X66 )
       != ( k2_struct_0 @ X67 ) )
      | ( v1_tops_1 @ X66 @ X67 )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('144',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X69 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X69 ) @ X68 ) @ X69 )
      | ( v2_tops_1 @ X68 @ X69 )
      | ~ ( l1_pre_topc @ X69 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('151',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('154',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('157',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','85','86','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d1bqVz76WL
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.81/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/1.01  % Solved by: fo/fo7.sh
% 0.81/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.01  % done 1710 iterations in 0.592s
% 0.81/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/1.01  % SZS output start Refutation
% 0.81/1.01  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.81/1.01  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.81/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.81/1.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.81/1.01  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.81/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.81/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.01  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.81/1.01  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.81/1.01  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.81/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.01  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.81/1.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.81/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.81/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.81/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.81/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.01  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.81/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.01  thf(t84_tops_1, conjecture,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01           ( ( v2_tops_1 @ B @ A ) <=>
% 0.81/1.01             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.81/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.01    (~( ![A:$i]:
% 0.81/1.01        ( ( l1_pre_topc @ A ) =>
% 0.81/1.01          ( ![B:$i]:
% 0.81/1.01            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01              ( ( v2_tops_1 @ B @ A ) <=>
% 0.81/1.01                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.81/1.01    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.81/1.01  thf('0', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.81/1.01        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('1', plain,
% 0.81/1.01      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.81/1.01       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.81/1.01      inference('split', [status(esa)], ['0'])).
% 0.81/1.01  thf('2', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('3', plain,
% 0.81/1.01      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('4', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(d4_tops_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01           ( ( v2_tops_1 @ B @ A ) <=>
% 0.81/1.01             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.81/1.01  thf('5', plain,
% 0.81/1.01      (![X68 : $i, X69 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 0.81/1.01          | ~ (v2_tops_1 @ X68 @ X69)
% 0.81/1.01          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X69) @ X68) @ X69)
% 0.81/1.01          | ~ (l1_pre_topc @ X69))),
% 0.81/1.01      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.81/1.01  thf('6', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.81/1.01        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.81/1.01  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('8', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(d5_subset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.01       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.81/1.01  thf('9', plain,
% 0.81/1.01      (![X36 : $i, X37 : $i]:
% 0.81/1.01         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.81/1.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.81/1.01  thf('10', plain,
% 0.81/1.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.81/1.01  thf(d3_struct_0, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.81/1.01  thf('11', plain,
% 0.81/1.01      (![X56 : $i]:
% 0.81/1.01         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.81/1.01  thf('12', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('13', plain,
% 0.81/1.01      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.81/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.81/1.01      inference('sup+', [status(thm)], ['11', '12'])).
% 0.81/1.01  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(dt_l1_pre_topc, axiom,
% 0.81/1.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.81/1.01  thf('15', plain,
% 0.81/1.01      (![X59 : $i]: ((l1_struct_0 @ X59) | ~ (l1_pre_topc @ X59))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.81/1.01  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.81/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.81/1.01  thf('17', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['13', '16'])).
% 0.81/1.01  thf('18', plain,
% 0.81/1.01      (![X36 : $i, X37 : $i]:
% 0.81/1.01         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.81/1.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.81/1.01  thf('19', plain,
% 0.81/1.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.81/1.01  thf('20', plain,
% 0.81/1.01      (![X56 : $i]:
% 0.81/1.01         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.81/1.01  thf('21', plain,
% 0.81/1.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.81/1.01  thf('22', plain,
% 0.81/1.01      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.81/1.01      inference('sup+', [status(thm)], ['20', '21'])).
% 0.81/1.01  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.81/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.81/1.01  thf('24', plain,
% 0.81/1.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['22', '23'])).
% 0.81/1.01  thf('25', plain,
% 0.81/1.01      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('sup+', [status(thm)], ['19', '24'])).
% 0.81/1.01  thf('26', plain,
% 0.81/1.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['10', '25'])).
% 0.81/1.01  thf('27', plain,
% 0.81/1.01      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.81/1.01        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['6', '7', '26'])).
% 0.81/1.01  thf('28', plain,
% 0.81/1.01      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.81/1.01         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['3', '27'])).
% 0.81/1.01  thf('29', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(dt_k3_subset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.01       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.81/1.01  thf('30', plain,
% 0.81/1.01      (![X39 : $i, X40 : $i]:
% 0.81/1.01         ((m1_subset_1 @ (k3_subset_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39))
% 0.81/1.01          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.81/1.01  thf('31', plain,
% 0.81/1.01      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.01  thf('32', plain,
% 0.81/1.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['10', '25'])).
% 0.81/1.01  thf('33', plain,
% 0.81/1.01      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['31', '32'])).
% 0.81/1.01  thf(d3_tops_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01           ( ( v1_tops_1 @ B @ A ) <=>
% 0.81/1.01             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.81/1.01  thf('34', plain,
% 0.81/1.01      (![X66 : $i, X67 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 0.81/1.01          | ~ (v1_tops_1 @ X66 @ X67)
% 0.81/1.01          | ((k2_pre_topc @ X67 @ X66) = (k2_struct_0 @ X67))
% 0.81/1.01          | ~ (l1_pre_topc @ X67))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.81/1.01  thf('35', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01            = (k2_struct_0 @ sk_A))
% 0.81/1.01        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['33', '34'])).
% 0.81/1.01  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('37', plain,
% 0.81/1.01      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01          = (k2_struct_0 @ sk_A))
% 0.81/1.01        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['35', '36'])).
% 0.81/1.01  thf('38', plain,
% 0.81/1.01      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01          = (k2_struct_0 @ sk_A)))
% 0.81/1.01         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['28', '37'])).
% 0.81/1.01  thf('39', plain,
% 0.81/1.01      (![X56 : $i]:
% 0.81/1.01         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.81/1.01  thf('40', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(d1_tops_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.01           ( ( k1_tops_1 @ A @ B ) =
% 0.81/1.01             ( k3_subset_1 @
% 0.81/1.01               ( u1_struct_0 @ A ) @ 
% 0.81/1.01               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.81/1.01  thf('41', plain,
% 0.81/1.01      (![X64 : $i, X65 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 0.81/1.01          | ((k1_tops_1 @ X65 @ X64)
% 0.81/1.01              = (k3_subset_1 @ (u1_struct_0 @ X65) @ 
% 0.81/1.01                 (k2_pre_topc @ X65 @ (k3_subset_1 @ (u1_struct_0 @ X65) @ X64))))
% 0.81/1.01          | ~ (l1_pre_topc @ X65))),
% 0.81/1.01      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.81/1.01  thf('42', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01               (k2_pre_topc @ sk_A @ 
% 0.81/1.01                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['40', '41'])).
% 0.81/1.01  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('44', plain,
% 0.81/1.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['10', '25'])).
% 0.81/1.01  thf('45', plain,
% 0.81/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.81/1.01      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.81/1.01  thf('46', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.81/1.01             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.81/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.81/1.01      inference('sup+', [status(thm)], ['39', '45'])).
% 0.81/1.01  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.81/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.81/1.01  thf('48', plain,
% 0.81/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.81/1.01            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.81/1.01      inference('demod', [status(thm)], ['46', '47'])).
% 0.81/1.01  thf('49', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.81/1.01         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['38', '48'])).
% 0.81/1.01  thf(dt_k2_subset_1, axiom,
% 0.81/1.01    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.81/1.01  thf('50', plain,
% 0.81/1.01      (![X38 : $i]: (m1_subset_1 @ (k2_subset_1 @ X38) @ (k1_zfmisc_1 @ X38))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.81/1.01  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.81/1.01  thf('51', plain, (![X35 : $i]: ((k2_subset_1 @ X35) = (X35))),
% 0.81/1.01      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.81/1.01  thf('52', plain, (![X38 : $i]: (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X38))),
% 0.81/1.01      inference('demod', [status(thm)], ['50', '51'])).
% 0.81/1.01  thf('53', plain,
% 0.81/1.01      (![X36 : $i, X37 : $i]:
% 0.81/1.01         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.81/1.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.81/1.01  thf('54', plain,
% 0.81/1.01      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['52', '53'])).
% 0.81/1.01  thf(t4_subset_1, axiom,
% 0.81/1.01    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.81/1.01  thf('55', plain,
% 0.81/1.01      (![X47 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 0.81/1.01      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.81/1.01  thf('56', plain, (![X38 : $i]: (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X38))),
% 0.81/1.01      inference('demod', [status(thm)], ['50', '51'])).
% 0.81/1.01  thf(t36_subset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.01       ( ![C:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.01           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.81/1.01             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.81/1.01  thf('57', plain,
% 0.81/1.01      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.81/1.01          | (r1_tarski @ (k3_subset_1 @ X45 @ X44) @ X46)
% 0.81/1.01          | ~ (r1_tarski @ (k3_subset_1 @ X45 @ X46) @ X44)
% 0.81/1.01          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.81/1.01  thf('58', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.81/1.01          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 0.81/1.01          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['56', '57'])).
% 0.81/1.01  thf('59', plain,
% 0.81/1.01      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['52', '53'])).
% 0.81/1.01  thf('60', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.81/1.01          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 0.81/1.01          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.81/1.01      inference('demod', [status(thm)], ['58', '59'])).
% 0.81/1.01  thf('61', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.81/1.01          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['55', '60'])).
% 0.81/1.01  thf('62', plain,
% 0.81/1.01      (![X47 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 0.81/1.01      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.81/1.01  thf('63', plain,
% 0.81/1.01      (![X36 : $i, X37 : $i]:
% 0.81/1.01         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.81/1.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.81/1.01  thf('64', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['62', '63'])).
% 0.81/1.01  thf(t2_boole, axiom,
% 0.81/1.01    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.81/1.01  thf('65', plain,
% 0.81/1.01      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_boole])).
% 0.81/1.01  thf(t12_setfam_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.81/1.01  thf('66', plain,
% 0.81/1.01      (![X48 : $i, X49 : $i]:
% 0.81/1.01         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 0.81/1.01      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.81/1.01  thf('67', plain,
% 0.81/1.01      (![X5 : $i]:
% 0.81/1.01         ((k1_setfam_1 @ (k2_tarski @ X5 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.81/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.81/1.01  thf(t100_xboole_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.81/1.01  thf('68', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X3 @ X4)
% 0.81/1.01           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/1.01  thf('69', plain,
% 0.81/1.01      (![X48 : $i, X49 : $i]:
% 0.81/1.01         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 0.81/1.01      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.81/1.01  thf('70', plain,
% 0.81/1.01      (![X3 : $i, X4 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X3 @ X4)
% 0.81/1.01           = (k5_xboole_0 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.81/1.01      inference('demod', [status(thm)], ['68', '69'])).
% 0.81/1.01  thf('71', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['67', '70'])).
% 0.81/1.01  thf(t5_boole, axiom,
% 0.81/1.01    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.81/1.01  thf('72', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.81/1.01      inference('cnf', [status(esa)], [t5_boole])).
% 0.81/1.01  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['71', '72'])).
% 0.81/1.01  thf('74', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.81/1.01      inference('demod', [status(thm)], ['64', '73'])).
% 0.81/1.01  thf(d10_xboole_0, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.01  thf('75', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('76', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.81/1.01      inference('simplify', [status(thm)], ['75'])).
% 0.81/1.01  thf('77', plain,
% 0.81/1.01      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)),
% 0.81/1.01      inference('demod', [status(thm)], ['61', '74', '76'])).
% 0.81/1.01  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.81/1.01  thf('78', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.81/1.01  thf('79', plain,
% 0.81/1.01      (![X0 : $i, X2 : $i]:
% 0.81/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('80', plain,
% 0.81/1.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['78', '79'])).
% 0.81/1.01  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['77', '80'])).
% 0.81/1.01  thf('82', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.81/1.01         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['49', '54', '81'])).
% 0.81/1.01  thf('83', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.81/1.01         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('split', [status(esa)], ['0'])).
% 0.81/1.01  thf('84', plain,
% 0.81/1.01      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.81/1.01         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.81/1.01             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['82', '83'])).
% 0.81/1.01  thf('85', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.81/1.01       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.81/1.01      inference('simplify', [status(thm)], ['84'])).
% 0.81/1.01  thf('86', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.81/1.01       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('87', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('88', plain,
% 0.81/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.81/1.01      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.81/1.01  thf('89', plain,
% 0.81/1.01      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['52', '53'])).
% 0.81/1.01  thf(t31_subset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.01       ( ![C:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.01           ( ( r1_tarski @ B @ C ) <=>
% 0.81/1.01             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.81/1.01  thf('90', plain,
% 0.81/1.01      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.81/1.01          | ~ (r1_tarski @ (k3_subset_1 @ X42 @ X41) @ 
% 0.81/1.01               (k3_subset_1 @ X42 @ X43))
% 0.81/1.01          | (r1_tarski @ X43 @ X41)
% 0.81/1.01          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.81/1.01  thf('91', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X0))
% 0.81/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 0.81/1.01          | (r1_tarski @ X0 @ X1)
% 0.81/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['89', '90'])).
% 0.81/1.01  thf('92', plain, (![X38 : $i]: (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X38))),
% 0.81/1.01      inference('demod', [status(thm)], ['50', '51'])).
% 0.81/1.01  thf('93', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X0))
% 0.81/1.01          | (r1_tarski @ X0 @ X1)
% 0.81/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.81/1.01      inference('demod', [status(thm)], ['91', '92'])).
% 0.81/1.01  thf('94', plain,
% 0.81/1.01      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.81/1.01           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.81/1.01        | ~ (m1_subset_1 @ 
% 0.81/1.01             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.81/1.01        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['88', '93'])).
% 0.81/1.01  thf('95', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['77', '80'])).
% 0.81/1.01  thf('96', plain,
% 0.81/1.01      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['31', '32'])).
% 0.81/1.01  thf(dt_k2_pre_topc, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( l1_pre_topc @ A ) & 
% 0.81/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/1.01       ( m1_subset_1 @
% 0.81/1.01         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.81/1.01  thf('97', plain,
% 0.81/1.01      (![X57 : $i, X58 : $i]:
% 0.81/1.01         (~ (l1_pre_topc @ X57)
% 0.81/1.01          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.81/1.01          | (m1_subset_1 @ (k2_pre_topc @ X57 @ X58) @ 
% 0.81/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ X57))))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.81/1.01  thf('98', plain,
% 0.81/1.01      (((m1_subset_1 @ 
% 0.81/1.01         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.81/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['96', '97'])).
% 0.81/1.01  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('100', plain,
% 0.81/1.01      ((m1_subset_1 @ 
% 0.81/1.01        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['98', '99'])).
% 0.81/1.01  thf('101', plain,
% 0.81/1.01      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.81/1.01        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.81/1.01      inference('demod', [status(thm)], ['94', '95', '100'])).
% 0.81/1.01  thf('102', plain,
% 0.81/1.01      (((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.81/1.01         | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['87', '101'])).
% 0.81/1.01  thf('103', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.81/1.01  thf('104', plain,
% 0.81/1.01      (((r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['102', '103'])).
% 0.81/1.01  thf('105', plain,
% 0.81/1.01      (![X0 : $i, X2 : $i]:
% 0.81/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('106', plain,
% 0.81/1.01      (((~ (r1_tarski @ 
% 0.81/1.01            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01            (u1_struct_0 @ sk_A))
% 0.81/1.01         | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01             = (u1_struct_0 @ sk_A))))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['104', '105'])).
% 0.81/1.01  thf('107', plain,
% 0.81/1.01      ((m1_subset_1 @ 
% 0.81/1.01        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['98', '99'])).
% 0.81/1.01  thf(t3_subset, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.81/1.01  thf('108', plain,
% 0.81/1.01      (![X50 : $i, X51 : $i]:
% 0.81/1.01         ((r1_tarski @ X50 @ X51) | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/1.01  thf('109', plain,
% 0.81/1.01      ((r1_tarski @ 
% 0.81/1.01        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01        (u1_struct_0 @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['107', '108'])).
% 0.81/1.01  thf('110', plain,
% 0.81/1.01      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01          = (u1_struct_0 @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['106', '109'])).
% 0.81/1.01  thf('111', plain,
% 0.81/1.01      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01          = (u1_struct_0 @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['106', '109'])).
% 0.81/1.01  thf('112', plain,
% 0.81/1.01      (((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.81/1.01            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.81/1.01      inference('demod', [status(thm)], ['46', '47'])).
% 0.81/1.01  thf('113', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.81/1.01          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup+', [status(thm)], ['111', '112'])).
% 0.81/1.01  thf('114', plain,
% 0.81/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('115', plain,
% 0.81/1.01      ((((k1_xboole_0)
% 0.81/1.01          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['113', '114'])).
% 0.81/1.01  thf('116', plain,
% 0.81/1.01      (![X47 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 0.81/1.01      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.81/1.01  thf('117', plain,
% 0.81/1.01      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.81/1.01          | (r1_tarski @ (k3_subset_1 @ X45 @ X44) @ X46)
% 0.81/1.01          | ~ (r1_tarski @ (k3_subset_1 @ X45 @ X46) @ X44)
% 0.81/1.01          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.81/1.01  thf('118', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.81/1.01          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0)
% 0.81/1.01          | (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['116', '117'])).
% 0.81/1.01  thf('119', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.81/1.01      inference('demod', [status(thm)], ['64', '73'])).
% 0.81/1.01  thf('120', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.81/1.01          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0)
% 0.81/1.01          | (r1_tarski @ X0 @ X1))),
% 0.81/1.01      inference('demod', [status(thm)], ['118', '119'])).
% 0.81/1.01  thf('121', plain,
% 0.81/1.01      (((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.81/1.01         | (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.81/1.01         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01              (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['115', '120'])).
% 0.81/1.01  thf('122', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.81/1.01  thf('123', plain,
% 0.81/1.01      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01          = (u1_struct_0 @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['106', '109'])).
% 0.81/1.01  thf('124', plain,
% 0.81/1.01      (![X56 : $i]:
% 0.81/1.01         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.81/1.01  thf('125', plain,
% 0.81/1.01      ((m1_subset_1 @ 
% 0.81/1.01        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['98', '99'])).
% 0.81/1.01  thf('126', plain,
% 0.81/1.01      (((m1_subset_1 @ 
% 0.81/1.01         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.81/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.81/1.01      inference('sup+', [status(thm)], ['124', '125'])).
% 0.81/1.01  thf('127', plain, ((l1_struct_0 @ sk_A)),
% 0.81/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.81/1.01  thf('128', plain,
% 0.81/1.01      ((m1_subset_1 @ 
% 0.81/1.01        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['126', '127'])).
% 0.81/1.01  thf('129', plain,
% 0.81/1.01      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.81/1.01         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup+', [status(thm)], ['123', '128'])).
% 0.81/1.01  thf('130', plain,
% 0.81/1.01      (((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['121', '122', '129'])).
% 0.81/1.01  thf('131', plain,
% 0.81/1.01      (![X0 : $i, X2 : $i]:
% 0.81/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('132', plain,
% 0.81/1.01      (((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.81/1.01         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.81/1.01  thf('133', plain,
% 0.81/1.01      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01          = (u1_struct_0 @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['106', '109'])).
% 0.81/1.01  thf('134', plain,
% 0.81/1.01      (![X56 : $i]:
% 0.81/1.01         (((k2_struct_0 @ X56) = (u1_struct_0 @ X56)) | ~ (l1_struct_0 @ X56))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.81/1.01  thf('135', plain,
% 0.81/1.01      ((r1_tarski @ 
% 0.81/1.01        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01        (u1_struct_0 @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['107', '108'])).
% 0.81/1.01  thf('136', plain,
% 0.81/1.01      (((r1_tarski @ 
% 0.81/1.01         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01         (k2_struct_0 @ sk_A))
% 0.81/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.81/1.01      inference('sup+', [status(thm)], ['134', '135'])).
% 0.81/1.01  thf('137', plain, ((l1_struct_0 @ sk_A)),
% 0.81/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.81/1.01  thf('138', plain,
% 0.81/1.01      ((r1_tarski @ 
% 0.81/1.01        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.81/1.01        (k2_struct_0 @ sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['136', '137'])).
% 0.81/1.01  thf('139', plain,
% 0.81/1.01      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup+', [status(thm)], ['133', '138'])).
% 0.81/1.01  thf('140', plain,
% 0.81/1.01      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['132', '139'])).
% 0.81/1.01  thf('141', plain,
% 0.81/1.01      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01          = (k2_struct_0 @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['110', '140'])).
% 0.81/1.01  thf('142', plain,
% 0.81/1.01      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.81/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['31', '32'])).
% 0.81/1.01  thf('143', plain,
% 0.81/1.01      (![X66 : $i, X67 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 0.81/1.01          | ((k2_pre_topc @ X67 @ X66) != (k2_struct_0 @ X67))
% 0.81/1.01          | (v1_tops_1 @ X66 @ X67)
% 0.81/1.01          | ~ (l1_pre_topc @ X67))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.81/1.01  thf('144', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.81/1.01        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01            != (k2_struct_0 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['142', '143'])).
% 0.81/1.01  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('146', plain,
% 0.81/1.01      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.81/1.01        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.81/1.01            != (k2_struct_0 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['144', '145'])).
% 0.81/1.01  thf('147', plain,
% 0.81/1.01      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.81/1.01         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['141', '146'])).
% 0.81/1.01  thf('148', plain,
% 0.81/1.01      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('simplify', [status(thm)], ['147'])).
% 0.81/1.01  thf('149', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('150', plain,
% 0.81/1.01      (![X68 : $i, X69 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 0.81/1.01          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X69) @ X68) @ X69)
% 0.81/1.01          | (v2_tops_1 @ X68 @ X69)
% 0.81/1.01          | ~ (l1_pre_topc @ X69))),
% 0.81/1.01      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.81/1.01  thf('151', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | (v2_tops_1 @ sk_B @ sk_A)
% 0.81/1.01        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['149', '150'])).
% 0.81/1.01  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('153', plain,
% 0.81/1.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.81/1.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['10', '25'])).
% 0.81/1.01  thf('154', plain,
% 0.81/1.01      (((v2_tops_1 @ sk_B @ sk_A)
% 0.81/1.01        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.81/1.01  thf('155', plain,
% 0.81/1.01      (((v2_tops_1 @ sk_B @ sk_A))
% 0.81/1.01         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['148', '154'])).
% 0.81/1.01  thf('156', plain,
% 0.81/1.01      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.81/1.01      inference('split', [status(esa)], ['0'])).
% 0.81/1.01  thf('157', plain,
% 0.81/1.01      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.81/1.01       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['155', '156'])).
% 0.81/1.01  thf('158', plain, ($false),
% 0.81/1.01      inference('sat_resolution*', [status(thm)], ['1', '85', '86', '157'])).
% 0.81/1.01  
% 0.81/1.01  % SZS output end Refutation
% 0.81/1.01  
% 0.81/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
