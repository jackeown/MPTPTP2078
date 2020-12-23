%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9j7hjBt4oH

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:13 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  251 (3320 expanded)
%              Number of leaves         :   38 (1038 expanded)
%              Depth                    :   25
%              Number of atoms          : 2017 (27249 expanded)
%              Number of equality atoms :  167 (2145 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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

thf('17',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tops_1 @ X30 @ X31 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('28',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('30',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','39'])).

thf('41',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','40'])).

thf('42',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v1_tops_1 @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = ( k2_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('57',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('58',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('59',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('62',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('64',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','62','63'])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('75',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('78',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('81',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('82',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('96',plain,(
    ! [X8: $i] :
      ( ( k1_subset_1 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('97',plain,(
    ! [X14: $i] :
      ( ( k2_subset_1 @ X14 )
      = ( k3_subset_1 @ X14 @ ( k1_subset_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('98',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('99',plain,(
    ! [X14: $i] :
      ( X14
      = ( k3_subset_1 @ X14 @ ( k1_subset_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['90','101'])).

thf('103',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('110',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('116',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('117',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('123',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','114','121','122'])).

thf('124',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('126',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('128',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('133',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('134',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('136',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['126','135'])).

thf('137',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','64'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','120'])).

thf('140',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('145',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('146',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('147',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('148',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('150',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('151',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('153',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('156',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['154','161'])).

thf('163',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','151','162'])).

thf('164',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('165',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('166',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','166'])).

thf('168',plain,
    ( ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['145','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['95','100'])).

thf('170',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('173',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('174',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('175',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('176',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['173','176'])).

thf('178',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('179',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['172','179'])).

thf('181',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('182',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('184',plain,
    ( ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['171','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('187',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('188',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['170','188'])).

thf('190',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('191',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_pre_topc @ X29 @ X28 )
       != ( k2_struct_0 @ X29 ) )
      | ( v1_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('192',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('196',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('197',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['189','197'])).

thf('199',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ( v2_tops_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('202',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('205',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('207',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['199','207'])).

thf('209',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('210',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','143','144','210'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9j7hjBt4oH
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.19/1.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.19/1.43  % Solved by: fo/fo7.sh
% 1.19/1.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.43  % done 3477 iterations in 0.957s
% 1.19/1.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.19/1.43  % SZS output start Refutation
% 1.19/1.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.19/1.43  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.19/1.43  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.19/1.43  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.19/1.43  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.19/1.43  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.19/1.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.19/1.43  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.19/1.43  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.19/1.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.19/1.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.19/1.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.43  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.43  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.19/1.43  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.43  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.19/1.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.43  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.19/1.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.43  thf(t84_tops_1, conjecture,
% 1.19/1.43    (![A:$i]:
% 1.19/1.43     ( ( l1_pre_topc @ A ) =>
% 1.19/1.43       ( ![B:$i]:
% 1.19/1.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.43           ( ( v2_tops_1 @ B @ A ) <=>
% 1.19/1.43             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.19/1.43  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.43    (~( ![A:$i]:
% 1.19/1.43        ( ( l1_pre_topc @ A ) =>
% 1.19/1.43          ( ![B:$i]:
% 1.19/1.43            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.43              ( ( v2_tops_1 @ B @ A ) <=>
% 1.19/1.43                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.19/1.43    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 1.19/1.43  thf('0', plain,
% 1.19/1.43      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 1.19/1.43        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('1', plain,
% 1.19/1.43      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.19/1.43       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.19/1.43      inference('split', [status(esa)], ['0'])).
% 1.19/1.43  thf(d3_struct_0, axiom,
% 1.19/1.43    (![A:$i]:
% 1.19/1.43     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.19/1.43  thf('2', plain,
% 1.19/1.43      (![X22 : $i]:
% 1.19/1.43         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.19/1.43  thf('3', plain,
% 1.19/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf(t3_subset, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.19/1.43  thf('4', plain,
% 1.19/1.43      (![X16 : $i, X17 : $i]:
% 1.19/1.43         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.43  thf('5', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.19/1.43      inference('sup-', [status(thm)], ['3', '4'])).
% 1.19/1.43  thf('6', plain,
% 1.19/1.43      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.19/1.43      inference('sup+', [status(thm)], ['2', '5'])).
% 1.19/1.43  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf(dt_l1_pre_topc, axiom,
% 1.19/1.43    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.19/1.43  thf('8', plain, (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 1.19/1.43      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.19/1.43  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 1.19/1.43      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.43  thf('10', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 1.19/1.43      inference('demod', [status(thm)], ['6', '9'])).
% 1.19/1.43  thf(t28_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.19/1.43  thf('11', plain,
% 1.19/1.43      (![X4 : $i, X5 : $i]:
% 1.19/1.43         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.19/1.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.43  thf('12', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 1.19/1.43      inference('sup-', [status(thm)], ['10', '11'])).
% 1.19/1.43  thf(commutativity_k3_xboole_0, axiom,
% 1.19/1.43    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.19/1.43  thf('13', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.43      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.19/1.43  thf(t100_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.19/1.43  thf('14', plain,
% 1.19/1.43      (![X2 : $i, X3 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X2 @ X3)
% 1.19/1.43           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.19/1.43  thf('15', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X0 @ X1)
% 1.19/1.43           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['13', '14'])).
% 1.19/1.43  thf('16', plain,
% 1.19/1.43      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup+', [status(thm)], ['12', '15'])).
% 1.19/1.43  thf('17', plain,
% 1.19/1.43      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('18', plain,
% 1.19/1.43      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('split', [status(esa)], ['17'])).
% 1.19/1.43  thf('19', plain,
% 1.19/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf(d4_tops_1, axiom,
% 1.19/1.43    (![A:$i]:
% 1.19/1.43     ( ( l1_pre_topc @ A ) =>
% 1.19/1.43       ( ![B:$i]:
% 1.19/1.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.43           ( ( v2_tops_1 @ B @ A ) <=>
% 1.19/1.43             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.19/1.43  thf('20', plain,
% 1.19/1.43      (![X30 : $i, X31 : $i]:
% 1.19/1.43         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.19/1.43          | ~ (v2_tops_1 @ X30 @ X31)
% 1.19/1.43          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 1.19/1.43          | ~ (l1_pre_topc @ X31))),
% 1.19/1.43      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.19/1.43  thf('21', plain,
% 1.19/1.43      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.43        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.19/1.43        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.19/1.43      inference('sup-', [status(thm)], ['19', '20'])).
% 1.19/1.43  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('23', plain,
% 1.19/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf(d5_subset_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.19/1.43       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.19/1.43  thf('24', plain,
% 1.19/1.43      (![X10 : $i, X11 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 1.19/1.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.19/1.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.19/1.43  thf('25', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup-', [status(thm)], ['23', '24'])).
% 1.19/1.43  thf('26', plain,
% 1.19/1.43      (![X22 : $i]:
% 1.19/1.43         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.19/1.43  thf('27', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup-', [status(thm)], ['23', '24'])).
% 1.19/1.43  thf('28', plain,
% 1.19/1.43      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43        | ~ (l1_struct_0 @ sk_A))),
% 1.19/1.43      inference('sup+', [status(thm)], ['26', '27'])).
% 1.19/1.43  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 1.19/1.43      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.43  thf('30', plain,
% 1.19/1.43      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['28', '29'])).
% 1.19/1.43  thf('31', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['25', '30'])).
% 1.19/1.43  thf('32', plain,
% 1.19/1.43      (![X22 : $i]:
% 1.19/1.43         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.19/1.43  thf('33', plain,
% 1.19/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('34', plain,
% 1.19/1.43      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.19/1.43        | ~ (l1_struct_0 @ sk_A))),
% 1.19/1.43      inference('sup+', [status(thm)], ['32', '33'])).
% 1.19/1.43  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 1.19/1.43      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.43  thf('36', plain,
% 1.19/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['34', '35'])).
% 1.19/1.43  thf('37', plain,
% 1.19/1.43      (![X10 : $i, X11 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 1.19/1.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.19/1.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.19/1.43  thf('38', plain,
% 1.19/1.43      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup-', [status(thm)], ['36', '37'])).
% 1.19/1.43  thf('39', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['31', '38'])).
% 1.19/1.43  thf('40', plain,
% 1.19/1.43      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.19/1.43        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.19/1.43      inference('demod', [status(thm)], ['21', '22', '39'])).
% 1.19/1.43  thf('41', plain,
% 1.19/1.43      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['18', '40'])).
% 1.19/1.43  thf('42', plain,
% 1.19/1.43      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['16', '41'])).
% 1.19/1.43  thf('43', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.19/1.43      inference('sup-', [status(thm)], ['3', '4'])).
% 1.19/1.43  thf('44', plain,
% 1.19/1.43      (![X4 : $i, X5 : $i]:
% 1.19/1.43         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.19/1.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.43  thf('45', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.19/1.43      inference('sup-', [status(thm)], ['43', '44'])).
% 1.19/1.43  thf('46', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X0 @ X1)
% 1.19/1.43           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['13', '14'])).
% 1.19/1.43  thf('47', plain,
% 1.19/1.43      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup+', [status(thm)], ['45', '46'])).
% 1.19/1.43  thf(t36_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.19/1.43  thf('48', plain,
% 1.19/1.43      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.19/1.43      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.19/1.43  thf('49', plain,
% 1.19/1.43      (![X16 : $i, X18 : $i]:
% 1.19/1.43         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 1.19/1.43      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.43  thf('50', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['48', '49'])).
% 1.19/1.43  thf('51', plain,
% 1.19/1.43      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.19/1.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['47', '50'])).
% 1.19/1.43  thf(d3_tops_1, axiom,
% 1.19/1.43    (![A:$i]:
% 1.19/1.43     ( ( l1_pre_topc @ A ) =>
% 1.19/1.43       ( ![B:$i]:
% 1.19/1.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.43           ( ( v1_tops_1 @ B @ A ) <=>
% 1.19/1.43             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 1.19/1.43  thf('52', plain,
% 1.19/1.43      (![X28 : $i, X29 : $i]:
% 1.19/1.43         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.19/1.43          | ~ (v1_tops_1 @ X28 @ X29)
% 1.19/1.43          | ((k2_pre_topc @ X29 @ X28) = (k2_struct_0 @ X29))
% 1.19/1.43          | ~ (l1_pre_topc @ X29))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.19/1.43  thf('53', plain,
% 1.19/1.43      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.43        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43            = (k2_struct_0 @ sk_A))
% 1.19/1.43        | ~ (v1_tops_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.19/1.43      inference('sup-', [status(thm)], ['51', '52'])).
% 1.19/1.43  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('55', plain,
% 1.19/1.43      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43          = (k2_struct_0 @ sk_A))
% 1.19/1.43        | ~ (v1_tops_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.19/1.43      inference('demod', [status(thm)], ['53', '54'])).
% 1.19/1.43  thf('56', plain,
% 1.19/1.43      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup+', [status(thm)], ['45', '46'])).
% 1.19/1.43  thf('57', plain,
% 1.19/1.43      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['28', '29'])).
% 1.19/1.43  thf('58', plain,
% 1.19/1.43      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup-', [status(thm)], ['36', '37'])).
% 1.19/1.43  thf('59', plain,
% 1.19/1.43      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['57', '58'])).
% 1.19/1.43  thf('60', plain,
% 1.19/1.43      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup+', [status(thm)], ['56', '59'])).
% 1.19/1.43  thf('61', plain,
% 1.19/1.43      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup+', [status(thm)], ['12', '15'])).
% 1.19/1.43  thf('62', plain,
% 1.19/1.43      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['60', '61'])).
% 1.19/1.43  thf('63', plain,
% 1.19/1.43      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['60', '61'])).
% 1.19/1.43  thf('64', plain,
% 1.19/1.43      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43          = (k2_struct_0 @ sk_A))
% 1.19/1.43        | ~ (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.19/1.43      inference('demod', [status(thm)], ['55', '62', '63'])).
% 1.19/1.43  thf('65', plain,
% 1.19/1.43      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43          = (k2_struct_0 @ sk_A)))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['42', '64'])).
% 1.19/1.43  thf('66', plain,
% 1.19/1.43      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.19/1.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['47', '50'])).
% 1.19/1.43  thf(dt_k2_pre_topc, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( ( l1_pre_topc @ A ) & 
% 1.19/1.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.19/1.43       ( m1_subset_1 @
% 1.19/1.43         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.19/1.43  thf('67', plain,
% 1.19/1.43      (![X23 : $i, X24 : $i]:
% 1.19/1.43         (~ (l1_pre_topc @ X23)
% 1.19/1.43          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.19/1.43          | (m1_subset_1 @ (k2_pre_topc @ X23 @ X24) @ 
% 1.19/1.43             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 1.19/1.43      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.19/1.43  thf('68', plain,
% 1.19/1.43      (((m1_subset_1 @ 
% 1.19/1.43         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.19/1.43        | ~ (l1_pre_topc @ sk_A))),
% 1.19/1.43      inference('sup-', [status(thm)], ['66', '67'])).
% 1.19/1.43  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('70', plain,
% 1.19/1.43      ((m1_subset_1 @ 
% 1.19/1.43        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['68', '69'])).
% 1.19/1.43  thf('71', plain,
% 1.19/1.43      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['60', '61'])).
% 1.19/1.43  thf('72', plain,
% 1.19/1.43      ((m1_subset_1 @ 
% 1.19/1.43        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['70', '71'])).
% 1.19/1.43  thf('73', plain,
% 1.19/1.43      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.19/1.43         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['65', '72'])).
% 1.19/1.43  thf(involutiveness_k3_subset_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.19/1.43       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.19/1.43  thf('74', plain,
% 1.19/1.43      (![X12 : $i, X13 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 1.19/1.43          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.19/1.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.19/1.43  thf('75', plain,
% 1.19/1.43      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.19/1.43          = (k2_struct_0 @ sk_A)))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['73', '74'])).
% 1.19/1.43  thf('76', plain,
% 1.19/1.43      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.19/1.43         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['65', '72'])).
% 1.19/1.43  thf('77', plain,
% 1.19/1.43      (![X10 : $i, X11 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 1.19/1.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.19/1.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.19/1.43  thf('78', plain,
% 1.19/1.43      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.19/1.43          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['76', '77'])).
% 1.19/1.43  thf('79', plain,
% 1.19/1.43      (![X22 : $i]:
% 1.19/1.43         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.19/1.43  thf('80', plain,
% 1.19/1.43      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.19/1.43          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['76', '77'])).
% 1.19/1.43  thf('81', plain,
% 1.19/1.43      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.19/1.43           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.19/1.43         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['79', '80'])).
% 1.19/1.43  thf(t4_subset_1, axiom,
% 1.19/1.43    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.19/1.43  thf('82', plain,
% 1.19/1.43      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 1.19/1.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.19/1.43  thf('83', plain,
% 1.19/1.43      (![X16 : $i, X17 : $i]:
% 1.19/1.43         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.43  thf('84', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.19/1.43      inference('sup-', [status(thm)], ['82', '83'])).
% 1.19/1.43  thf('85', plain,
% 1.19/1.43      (![X4 : $i, X5 : $i]:
% 1.19/1.43         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.19/1.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.43  thf('86', plain,
% 1.19/1.43      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['84', '85'])).
% 1.19/1.43  thf('87', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.43      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.19/1.43  thf('88', plain,
% 1.19/1.43      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['86', '87'])).
% 1.19/1.43  thf('89', plain,
% 1.19/1.43      (![X2 : $i, X3 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X2 @ X3)
% 1.19/1.43           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.19/1.43  thf('90', plain,
% 1.19/1.43      (![X0 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['88', '89'])).
% 1.19/1.43  thf('91', plain,
% 1.19/1.43      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 1.19/1.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.19/1.43  thf('92', plain,
% 1.19/1.43      (![X10 : $i, X11 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 1.19/1.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.19/1.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.19/1.43  thf('93', plain,
% 1.19/1.43      (![X0 : $i]:
% 1.19/1.43         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['91', '92'])).
% 1.19/1.43  thf('94', plain,
% 1.19/1.43      (![X0 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['88', '89'])).
% 1.19/1.43  thf('95', plain,
% 1.19/1.43      (![X0 : $i]:
% 1.19/1.43         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('demod', [status(thm)], ['93', '94'])).
% 1.19/1.43  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.19/1.43  thf('96', plain, (![X8 : $i]: ((k1_subset_1 @ X8) = (k1_xboole_0))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.19/1.43  thf(t22_subset_1, axiom,
% 1.19/1.43    (![A:$i]:
% 1.19/1.43     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.19/1.43  thf('97', plain,
% 1.19/1.43      (![X14 : $i]:
% 1.19/1.43         ((k2_subset_1 @ X14) = (k3_subset_1 @ X14 @ (k1_subset_1 @ X14)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.19/1.43  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.19/1.43  thf('98', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 1.19/1.43      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.19/1.43  thf('99', plain,
% 1.19/1.43      (![X14 : $i]: ((X14) = (k3_subset_1 @ X14 @ (k1_subset_1 @ X14)))),
% 1.19/1.43      inference('demod', [status(thm)], ['97', '98'])).
% 1.19/1.43  thf('100', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['96', '99'])).
% 1.19/1.43  thf('101', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['95', '100'])).
% 1.19/1.43  thf('102', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.19/1.43      inference('demod', [status(thm)], ['90', '101'])).
% 1.19/1.43  thf('103', plain,
% 1.19/1.43      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.19/1.43      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.19/1.43  thf('104', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.19/1.43      inference('sup+', [status(thm)], ['102', '103'])).
% 1.19/1.43  thf('105', plain,
% 1.19/1.43      (![X16 : $i, X18 : $i]:
% 1.19/1.43         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 1.19/1.43      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.43  thf('106', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['104', '105'])).
% 1.19/1.43  thf('107', plain,
% 1.19/1.43      (![X10 : $i, X11 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 1.19/1.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.19/1.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.19/1.43  thf('108', plain,
% 1.19/1.43      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['106', '107'])).
% 1.19/1.43  thf('109', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.19/1.43      inference('sup+', [status(thm)], ['102', '103'])).
% 1.19/1.43  thf('110', plain,
% 1.19/1.43      (![X4 : $i, X5 : $i]:
% 1.19/1.43         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.19/1.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.43  thf('111', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['109', '110'])).
% 1.19/1.43  thf('112', plain,
% 1.19/1.43      (![X2 : $i, X3 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X2 @ X3)
% 1.19/1.43           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.19/1.43  thf('113', plain,
% 1.19/1.43      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['111', '112'])).
% 1.19/1.43  thf('114', plain,
% 1.19/1.43      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.19/1.43      inference('demod', [status(thm)], ['108', '113'])).
% 1.19/1.43  thf('115', plain,
% 1.19/1.43      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.19/1.43      inference('demod', [status(thm)], ['108', '113'])).
% 1.19/1.43  thf('116', plain,
% 1.19/1.43      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 1.19/1.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.19/1.43  thf('117', plain,
% 1.19/1.43      (![X12 : $i, X13 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 1.19/1.43          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.19/1.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.19/1.43  thf('118', plain,
% 1.19/1.43      (![X0 : $i]:
% 1.19/1.43         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['116', '117'])).
% 1.19/1.43  thf('119', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['96', '99'])).
% 1.19/1.43  thf('120', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.19/1.43      inference('demod', [status(thm)], ['118', '119'])).
% 1.19/1.43  thf('121', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['115', '120'])).
% 1.19/1.43  thf('122', plain, ((l1_struct_0 @ sk_A)),
% 1.19/1.43      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.43  thf('123', plain,
% 1.19/1.43      ((((k1_xboole_0)
% 1.19/1.43          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['81', '114', '121', '122'])).
% 1.19/1.43  thf('124', plain,
% 1.19/1.43      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.19/1.43          = (k1_xboole_0)))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['78', '123'])).
% 1.19/1.43  thf('125', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['96', '99'])).
% 1.19/1.43  thf('126', plain,
% 1.19/1.43      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['75', '124', '125'])).
% 1.19/1.43  thf('127', plain,
% 1.19/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf(d1_tops_1, axiom,
% 1.19/1.43    (![A:$i]:
% 1.19/1.43     ( ( l1_pre_topc @ A ) =>
% 1.19/1.43       ( ![B:$i]:
% 1.19/1.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.43           ( ( k1_tops_1 @ A @ B ) =
% 1.19/1.43             ( k3_subset_1 @
% 1.19/1.43               ( u1_struct_0 @ A ) @ 
% 1.19/1.43               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.19/1.43  thf('128', plain,
% 1.19/1.43      (![X26 : $i, X27 : $i]:
% 1.19/1.43         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.19/1.43          | ((k1_tops_1 @ X27 @ X26)
% 1.19/1.43              = (k3_subset_1 @ (u1_struct_0 @ X27) @ 
% 1.19/1.43                 (k2_pre_topc @ X27 @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26))))
% 1.19/1.43          | ~ (l1_pre_topc @ X27))),
% 1.19/1.43      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.19/1.43  thf('129', plain,
% 1.19/1.43      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.43        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.19/1.43            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43               (k2_pre_topc @ sk_A @ 
% 1.19/1.43                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['127', '128'])).
% 1.19/1.43  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('131', plain,
% 1.19/1.43      (((k1_tops_1 @ sk_A @ sk_B)
% 1.19/1.43         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.19/1.43      inference('demod', [status(thm)], ['129', '130'])).
% 1.19/1.43  thf('132', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['31', '38'])).
% 1.19/1.43  thf('133', plain,
% 1.19/1.43      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup+', [status(thm)], ['12', '15'])).
% 1.19/1.43  thf('134', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['132', '133'])).
% 1.19/1.43  thf('135', plain,
% 1.19/1.43      (((k1_tops_1 @ sk_A @ sk_B)
% 1.19/1.43         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.19/1.43      inference('demod', [status(thm)], ['131', '134'])).
% 1.19/1.43  thf('136', plain,
% 1.19/1.43      ((((k1_tops_1 @ sk_A @ sk_B)
% 1.19/1.43          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.19/1.43             (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['126', '135'])).
% 1.19/1.43  thf('137', plain,
% 1.19/1.43      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43          = (k2_struct_0 @ sk_A)))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['42', '64'])).
% 1.19/1.43  thf('138', plain,
% 1.19/1.43      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.19/1.43      inference('demod', [status(thm)], ['108', '113'])).
% 1.19/1.43  thf('139', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['115', '120'])).
% 1.19/1.43  thf('140', plain,
% 1.19/1.43      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.19/1.43         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 1.19/1.43  thf('141', plain,
% 1.19/1.43      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 1.19/1.43         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('split', [status(esa)], ['0'])).
% 1.19/1.43  thf('142', plain,
% 1.19/1.43      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.19/1.43         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 1.19/1.43             ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['140', '141'])).
% 1.19/1.43  thf('143', plain,
% 1.19/1.43      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.19/1.43       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.19/1.43      inference('simplify', [status(thm)], ['142'])).
% 1.19/1.43  thf('144', plain,
% 1.19/1.43      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.19/1.43       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.19/1.43      inference('split', [status(esa)], ['17'])).
% 1.19/1.43  thf('145', plain,
% 1.19/1.43      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('split', [status(esa)], ['17'])).
% 1.19/1.43  thf('146', plain,
% 1.19/1.43      ((m1_subset_1 @ 
% 1.19/1.43        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['70', '71'])).
% 1.19/1.43  thf('147', plain,
% 1.19/1.43      (![X12 : $i, X13 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 1.19/1.43          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.19/1.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.19/1.43  thf('148', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43          (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.19/1.43         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['146', '147'])).
% 1.19/1.43  thf('149', plain,
% 1.19/1.43      ((m1_subset_1 @ 
% 1.19/1.43        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['70', '71'])).
% 1.19/1.43  thf('150', plain,
% 1.19/1.43      (![X10 : $i, X11 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 1.19/1.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.19/1.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.19/1.43  thf('151', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 1.19/1.43         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['149', '150'])).
% 1.19/1.43  thf('152', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['48', '49'])).
% 1.19/1.43  thf('153', plain,
% 1.19/1.43      (![X10 : $i, X11 : $i]:
% 1.19/1.43         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 1.19/1.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.19/1.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.19/1.43  thf('154', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.19/1.43           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['152', '153'])).
% 1.19/1.43  thf('155', plain,
% 1.19/1.43      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.19/1.43      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.19/1.43  thf('156', plain,
% 1.19/1.43      (![X4 : $i, X5 : $i]:
% 1.19/1.43         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.19/1.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.43  thf('157', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.19/1.43           = (k4_xboole_0 @ X0 @ X1))),
% 1.19/1.43      inference('sup-', [status(thm)], ['155', '156'])).
% 1.19/1.43  thf('158', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.43      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.19/1.43  thf('159', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.19/1.43           = (k4_xboole_0 @ X0 @ X1))),
% 1.19/1.43      inference('demod', [status(thm)], ['157', '158'])).
% 1.19/1.43  thf('160', plain,
% 1.19/1.43      (![X2 : $i, X3 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X2 @ X3)
% 1.19/1.43           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.19/1.43  thf('161', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.19/1.43           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['159', '160'])).
% 1.19/1.43  thf('162', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.19/1.43           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.19/1.43      inference('demod', [status(thm)], ['154', '161'])).
% 1.19/1.43  thf('163', plain,
% 1.19/1.43      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43          (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.19/1.43         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.19/1.43      inference('demod', [status(thm)], ['148', '151', '162'])).
% 1.19/1.43  thf('164', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 1.19/1.43         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['149', '150'])).
% 1.19/1.43  thf('165', plain,
% 1.19/1.43      (((k1_tops_1 @ sk_A @ sk_B)
% 1.19/1.43         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.19/1.43      inference('demod', [status(thm)], ['131', '134'])).
% 1.19/1.43  thf('166', plain,
% 1.19/1.43      (((k1_tops_1 @ sk_A @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.43            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.19/1.43      inference('sup+', [status(thm)], ['164', '165'])).
% 1.19/1.43  thf('167', plain,
% 1.19/1.43      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.19/1.43         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.19/1.43      inference('demod', [status(thm)], ['163', '166'])).
% 1.19/1.43  thf('168', plain,
% 1.19/1.43      ((((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.19/1.43          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('sup+', [status(thm)], ['145', '167'])).
% 1.19/1.43  thf('169', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['95', '100'])).
% 1.19/1.43  thf('170', plain,
% 1.19/1.43      ((((u1_struct_0 @ sk_A)
% 1.19/1.43          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('demod', [status(thm)], ['168', '169'])).
% 1.19/1.43  thf('171', plain,
% 1.19/1.43      (![X22 : $i]:
% 1.19/1.43         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.19/1.43  thf('172', plain,
% 1.19/1.43      ((((u1_struct_0 @ sk_A)
% 1.19/1.43          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('demod', [status(thm)], ['168', '169'])).
% 1.19/1.43  thf('173', plain,
% 1.19/1.43      (![X22 : $i]:
% 1.19/1.43         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.19/1.43  thf('174', plain,
% 1.19/1.43      ((m1_subset_1 @ 
% 1.19/1.43        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['70', '71'])).
% 1.19/1.43  thf('175', plain,
% 1.19/1.43      (![X16 : $i, X17 : $i]:
% 1.19/1.43         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.43  thf('176', plain,
% 1.19/1.43      ((r1_tarski @ 
% 1.19/1.43        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43        (u1_struct_0 @ sk_A))),
% 1.19/1.43      inference('sup-', [status(thm)], ['174', '175'])).
% 1.19/1.43  thf('177', plain,
% 1.19/1.43      (((r1_tarski @ 
% 1.19/1.43         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43         (k2_struct_0 @ sk_A))
% 1.19/1.43        | ~ (l1_struct_0 @ sk_A))),
% 1.19/1.43      inference('sup+', [status(thm)], ['173', '176'])).
% 1.19/1.43  thf('178', plain, ((l1_struct_0 @ sk_A)),
% 1.19/1.43      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.43  thf('179', plain,
% 1.19/1.43      ((r1_tarski @ 
% 1.19/1.43        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.19/1.43        (k2_struct_0 @ sk_A))),
% 1.19/1.43      inference('demod', [status(thm)], ['177', '178'])).
% 1.19/1.43  thf('180', plain,
% 1.19/1.43      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('sup+', [status(thm)], ['172', '179'])).
% 1.19/1.43  thf('181', plain,
% 1.19/1.43      (![X4 : $i, X5 : $i]:
% 1.19/1.43         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 1.19/1.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.43  thf('182', plain,
% 1.19/1.43      ((((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.19/1.43          = (u1_struct_0 @ sk_A)))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['180', '181'])).
% 1.19/1.43  thf('183', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.43      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.19/1.43  thf('184', plain,
% 1.19/1.43      ((((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.19/1.43          = (u1_struct_0 @ sk_A)))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('demod', [status(thm)], ['182', '183'])).
% 1.19/1.43  thf('185', plain,
% 1.19/1.43      (((((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.19/1.43           = (u1_struct_0 @ sk_A))
% 1.19/1.43         | ~ (l1_struct_0 @ sk_A)))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('sup+', [status(thm)], ['171', '184'])).
% 1.19/1.43  thf('186', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['109', '110'])).
% 1.19/1.43  thf('187', plain, ((l1_struct_0 @ sk_A)),
% 1.19/1.43      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.43  thf('188', plain,
% 1.19/1.43      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('demod', [status(thm)], ['185', '186', '187'])).
% 1.19/1.43  thf('189', plain,
% 1.19/1.43      ((((k2_struct_0 @ sk_A)
% 1.19/1.43          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('demod', [status(thm)], ['170', '188'])).
% 1.19/1.43  thf('190', plain,
% 1.19/1.43      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.19/1.43        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('sup+', [status(thm)], ['47', '50'])).
% 1.19/1.43  thf('191', plain,
% 1.19/1.43      (![X28 : $i, X29 : $i]:
% 1.19/1.43         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.19/1.43          | ((k2_pre_topc @ X29 @ X28) != (k2_struct_0 @ X29))
% 1.19/1.43          | (v1_tops_1 @ X28 @ X29)
% 1.19/1.43          | ~ (l1_pre_topc @ X29))),
% 1.19/1.43      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.19/1.43  thf('192', plain,
% 1.19/1.43      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.43        | (v1_tops_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.19/1.43        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43            != (k2_struct_0 @ sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['190', '191'])).
% 1.19/1.43  thf('193', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('194', plain,
% 1.19/1.43      (((v1_tops_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.19/1.43        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43            != (k2_struct_0 @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['192', '193'])).
% 1.19/1.43  thf('195', plain,
% 1.19/1.43      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['60', '61'])).
% 1.19/1.43  thf('196', plain,
% 1.19/1.43      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['60', '61'])).
% 1.19/1.43  thf('197', plain,
% 1.19/1.43      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.19/1.43        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.19/1.43            != (k2_struct_0 @ sk_A)))),
% 1.19/1.43      inference('demod', [status(thm)], ['194', '195', '196'])).
% 1.19/1.43  thf('198', plain,
% 1.19/1.43      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 1.19/1.43         | (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['189', '197'])).
% 1.19/1.43  thf('199', plain,
% 1.19/1.43      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('simplify', [status(thm)], ['198'])).
% 1.19/1.43  thf('200', plain,
% 1.19/1.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('201', plain,
% 1.19/1.43      (![X30 : $i, X31 : $i]:
% 1.19/1.43         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.19/1.43          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 1.19/1.43          | (v2_tops_1 @ X30 @ X31)
% 1.19/1.43          | ~ (l1_pre_topc @ X31))),
% 1.19/1.43      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.19/1.43  thf('202', plain,
% 1.19/1.43      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.43        | (v2_tops_1 @ sk_B @ sk_A)
% 1.19/1.43        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.19/1.43      inference('sup-', [status(thm)], ['200', '201'])).
% 1.19/1.43  thf('203', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('204', plain,
% 1.19/1.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('demod', [status(thm)], ['31', '38'])).
% 1.19/1.43  thf('205', plain,
% 1.19/1.43      (((v2_tops_1 @ sk_B @ sk_A)
% 1.19/1.43        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.19/1.43      inference('demod', [status(thm)], ['202', '203', '204'])).
% 1.19/1.43  thf('206', plain,
% 1.19/1.43      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.19/1.43         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.19/1.43      inference('sup+', [status(thm)], ['12', '15'])).
% 1.19/1.43  thf('207', plain,
% 1.19/1.43      (((v2_tops_1 @ sk_B @ sk_A)
% 1.19/1.43        | ~ (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.19/1.43      inference('demod', [status(thm)], ['205', '206'])).
% 1.19/1.43  thf('208', plain,
% 1.19/1.43      (((v2_tops_1 @ sk_B @ sk_A))
% 1.19/1.43         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['199', '207'])).
% 1.19/1.43  thf('209', plain,
% 1.19/1.43      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.19/1.43      inference('split', [status(esa)], ['0'])).
% 1.19/1.43  thf('210', plain,
% 1.19/1.43      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.19/1.43       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.19/1.43      inference('sup-', [status(thm)], ['208', '209'])).
% 1.19/1.43  thf('211', plain, ($false),
% 1.19/1.43      inference('sat_resolution*', [status(thm)], ['1', '143', '144', '210'])).
% 1.19/1.43  
% 1.19/1.43  % SZS output end Refutation
% 1.19/1.43  
% 1.19/1.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
