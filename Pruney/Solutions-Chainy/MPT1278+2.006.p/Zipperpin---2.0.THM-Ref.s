%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.md9rH1iOzq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:40 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 537 expanded)
%              Number of leaves         :   36 ( 177 expanded)
%              Depth                    :   16
%              Number of atoms          : 1084 (6232 expanded)
%              Number of equality atoms :   66 ( 326 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t97_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v3_tops_1 @ B @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ ( k2_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tops_1 @ X29 @ X30 )
      | ( ( k1_tops_1 @ X30 @ X29 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v2_tops_1 @ X31 @ X32 )
      | ~ ( v3_tops_1 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
              = ( k2_pre_topc @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_pre_topc @ X24 @ ( k1_tops_1 @ X24 @ ( k2_pre_topc @ X24 @ X23 ) ) )
        = ( k2_pre_topc @ X24 @ X23 ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t59_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_tops_1 @ X18 @ X17 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','13'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tops_1 @ X29 @ X30 )
      | ( ( k1_tops_1 @ X30 @ X29 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_tops_1 @ X15 @ X16 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X16 @ X15 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','48'])).

thf('50',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','35','36'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('53',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','35','36'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X21 @ ( k1_tops_1 @ X21 @ X22 ) )
        = ( k1_tops_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('56',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('58',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('61',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ X1 )
        = ( k4_xboole_0 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('67',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_tops_1 @ X18 @ X17 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ k1_xboole_0 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_1 @ X0 @ k1_xboole_0 )
        = ( k4_xboole_0 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ k1_xboole_0 )
        = ( k4_xboole_0 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['60','70'])).

thf('72',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_tops_1 @ sk_A @ k1_xboole_0 )
    = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','35','36'])).

thf('76',plain,
    ( ( k2_tops_1 @ sk_A @ k1_xboole_0 )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23','37','51','74','75'])).

thf('77',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t77_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v4_pre_topc @ X27 @ X28 )
      | ( ( k2_tops_1 @ X28 @ X27 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ ( k1_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_tops_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ k1_xboole_0 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('86',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('89',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['76','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('100',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['18','98','99'])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.md9rH1iOzq
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 171 iterations in 0.083s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.53  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.36/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.36/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.53  thf(t97_tops_1, conjecture,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.36/0.53             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i]:
% 0.36/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53          ( ![B:$i]:
% 0.36/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.36/0.53                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.36/0.53  thf('0', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t74_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( k1_tops_1 @ A @ B ) =
% 0.36/0.53             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      (![X25 : $i, X26 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.53          | ((k1_tops_1 @ X26 @ X25)
% 0.36/0.53              = (k7_subset_1 @ (u1_struct_0 @ X26) @ X25 @ 
% 0.36/0.53                 (k2_tops_1 @ X26 @ X25)))
% 0.36/0.53          | ~ (l1_pre_topc @ X26))),
% 0.36/0.53      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.53               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t84_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v2_tops_1 @ B @ A ) <=>
% 0.36/0.53             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.36/0.53  thf('5', plain,
% 0.36/0.53      (![X29 : $i, X30 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.36/0.53          | ~ (v2_tops_1 @ X29 @ X30)
% 0.36/0.53          | ((k1_tops_1 @ X30 @ X29) = (k1_xboole_0))
% 0.36/0.53          | ~ (l1_pre_topc @ X30))),
% 0.36/0.53      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.36/0.53  thf('6', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.36/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.53  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t92_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      (![X31 : $i, X32 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.36/0.53          | (v2_tops_1 @ X31 @ X32)
% 0.36/0.53          | ~ (v3_tops_1 @ X31 @ X32)
% 0.36/0.53          | ~ (l1_pre_topc @ X32))),
% 0.36/0.53      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.36/0.53        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.53  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('12', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('13', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.36/0.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.36/0.53  thf('14', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['6', '7', '13'])).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.36/0.53          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['2', '3', '14', '17'])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t59_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v3_pre_topc @ B @ A ) =>
% 0.36/0.53             ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) =
% 0.36/0.53               ( k2_pre_topc @ A @ B ) ) ) ) ) ))).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      (![X23 : $i, X24 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.36/0.53          | ((k2_pre_topc @ X24 @ (k1_tops_1 @ X24 @ (k2_pre_topc @ X24 @ X23)))
% 0.36/0.53              = (k2_pre_topc @ X24 @ X23))
% 0.36/0.53          | ~ (v3_pre_topc @ X23 @ X24)
% 0.36/0.53          | ~ (l1_pre_topc @ X24))),
% 0.36/0.53      inference('cnf', [status(esa)], [t59_tops_1])).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.36/0.53        | ((k2_pre_topc @ sk_A @ 
% 0.36/0.53            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.36/0.53            = (k2_pre_topc @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('23', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(l78_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.53             ( k7_subset_1 @
% 0.36/0.53               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.36/0.53               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      (![X17 : $i, X18 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.36/0.53          | ((k2_tops_1 @ X18 @ X17)
% 0.36/0.53              = (k7_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.36/0.53                 (k2_pre_topc @ X18 @ X17) @ (k1_tops_1 @ X18 @ X17)))
% 0.36/0.53          | ~ (l1_pre_topc @ X18))),
% 0.36/0.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.36/0.53  thf('26', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('28', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['6', '7', '13'])).
% 0.36/0.53  thf('29', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(dt_k2_pre_topc, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.53       ( m1_subset_1 @
% 0.36/0.53         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.53  thf('30', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X13)
% 0.36/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.53          | (m1_subset_1 @ (k2_pre_topc @ X13 @ X14) @ 
% 0.36/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.36/0.53  thf('31', plain,
% 0.36/0.53      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('33', plain,
% 0.36/0.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.53  thf('34', plain,
% 0.36/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.36/0.53          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.53  thf('35', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.53           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.53  thf(t3_boole, axiom,
% 0.36/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.53  thf('36', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.53  thf('37', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['26', '27', '28', '35', '36'])).
% 0.36/0.53  thf('38', plain,
% 0.36/0.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.53  thf('39', plain,
% 0.36/0.53      (![X29 : $i, X30 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.36/0.53          | ~ (v2_tops_1 @ X29 @ X30)
% 0.36/0.53          | ((k1_tops_1 @ X30 @ X29) = (k1_xboole_0))
% 0.36/0.53          | ~ (l1_pre_topc @ X30))),
% 0.36/0.53      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.36/0.53  thf('40', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.36/0.53        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.53  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('42', plain,
% 0.36/0.53      ((((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.36/0.53        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.53  thf('43', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(d5_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v3_tops_1 @ B @ A ) <=>
% 0.36/0.53             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.36/0.53  thf('44', plain,
% 0.36/0.53      (![X15 : $i, X16 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.53          | ~ (v3_tops_1 @ X15 @ X16)
% 0.36/0.53          | (v2_tops_1 @ (k2_pre_topc @ X16 @ X15) @ X16)
% 0.36/0.53          | ~ (l1_pre_topc @ X16))),
% 0.36/0.53      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.36/0.53  thf('45', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.36/0.53        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.53  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('47', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('48', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.36/0.53      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['42', '48'])).
% 0.36/0.53  thf('50', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['26', '27', '28', '35', '36'])).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.36/0.53  thf('52', plain,
% 0.36/0.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.53  thf('53', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['26', '27', '28', '35', '36'])).
% 0.36/0.53  thf('54', plain,
% 0.36/0.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.53  thf(projectivity_k1_tops_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.53       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.36/0.53  thf('55', plain,
% 0.36/0.53      (![X21 : $i, X22 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X21)
% 0.36/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.36/0.53          | ((k1_tops_1 @ X21 @ (k1_tops_1 @ X21 @ X22))
% 0.36/0.53              = (k1_tops_1 @ X21 @ X22)))),
% 0.36/0.53      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.36/0.53  thf('56', plain,
% 0.36/0.53      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.53          = (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.53  thf('57', plain,
% 0.36/0.53      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.36/0.53  thf('58', plain,
% 0.36/0.53      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.36/0.53  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('60', plain, (((k1_tops_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.36/0.53  thf(t4_subset_1, axiom,
% 0.36/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.53  thf('61', plain,
% 0.36/0.53      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.53  thf('62', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X13)
% 0.36/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.53          | (m1_subset_1 @ (k2_pre_topc @ X13 @ X14) @ 
% 0.36/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.36/0.53  thf('63', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((m1_subset_1 @ (k2_pre_topc @ X0 @ k1_xboole_0) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.36/0.53          | ~ (l1_pre_topc @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.53  thf('64', plain,
% 0.36/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.36/0.53          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.53  thf('65', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X0)
% 0.36/0.53          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.36/0.53              (k2_pre_topc @ X0 @ k1_xboole_0) @ X1)
% 0.36/0.53              = (k4_xboole_0 @ (k2_pre_topc @ X0 @ k1_xboole_0) @ X1)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.53  thf('66', plain,
% 0.36/0.53      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.53  thf('67', plain,
% 0.36/0.53      (![X17 : $i, X18 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.36/0.53          | ((k2_tops_1 @ X18 @ X17)
% 0.36/0.53              = (k7_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.36/0.53                 (k2_pre_topc @ X18 @ X17) @ (k1_tops_1 @ X18 @ X17)))
% 0.36/0.53          | ~ (l1_pre_topc @ X18))),
% 0.36/0.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.36/0.53  thf('68', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X0)
% 0.36/0.53          | ((k2_tops_1 @ X0 @ k1_xboole_0)
% 0.36/0.53              = (k7_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.36/0.53                 (k2_pre_topc @ X0 @ k1_xboole_0) @ 
% 0.36/0.53                 (k1_tops_1 @ X0 @ k1_xboole_0))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.53  thf('69', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (((k2_tops_1 @ X0 @ k1_xboole_0)
% 0.36/0.53            = (k4_xboole_0 @ (k2_pre_topc @ X0 @ k1_xboole_0) @ 
% 0.36/0.53               (k1_tops_1 @ X0 @ k1_xboole_0)))
% 0.36/0.53          | ~ (l1_pre_topc @ X0)
% 0.36/0.53          | ~ (l1_pre_topc @ X0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['65', '68'])).
% 0.36/0.53  thf('70', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (l1_pre_topc @ X0)
% 0.36/0.53          | ((k2_tops_1 @ X0 @ k1_xboole_0)
% 0.36/0.53              = (k4_xboole_0 @ (k2_pre_topc @ X0 @ k1_xboole_0) @ 
% 0.36/0.53                 (k1_tops_1 @ X0 @ k1_xboole_0))))),
% 0.36/0.53      inference('simplify', [status(thm)], ['69'])).
% 0.36/0.53  thf('71', plain,
% 0.36/0.53      ((((k2_tops_1 @ sk_A @ k1_xboole_0)
% 0.36/0.53          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ k1_xboole_0) @ k1_xboole_0))
% 0.36/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.53      inference('sup+', [status(thm)], ['60', '70'])).
% 0.36/0.53  thf('72', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.53  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('74', plain,
% 0.36/0.53      (((k2_tops_1 @ sk_A @ k1_xboole_0) = (k2_pre_topc @ sk_A @ k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.36/0.53  thf('75', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['26', '27', '28', '35', '36'])).
% 0.36/0.53  thf('76', plain,
% 0.36/0.53      (((k2_tops_1 @ sk_A @ k1_xboole_0) = (k2_tops_1 @ sk_A @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)],
% 0.36/0.53                ['21', '22', '23', '37', '51', '74', '75'])).
% 0.36/0.53  thf('77', plain,
% 0.36/0.53      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.53  thf(cc2_pre_topc, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.36/0.53  thf('78', plain,
% 0.36/0.53      (![X11 : $i, X12 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.36/0.53          | (v4_pre_topc @ X11 @ X12)
% 0.36/0.53          | ~ (v1_xboole_0 @ X11)
% 0.36/0.53          | ~ (l1_pre_topc @ X12)
% 0.36/0.53          | ~ (v2_pre_topc @ X12))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.36/0.53  thf('79', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v2_pre_topc @ X0)
% 0.36/0.53          | ~ (l1_pre_topc @ X0)
% 0.36/0.53          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.53          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.36/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.53  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.53  thf('81', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v2_pre_topc @ X0)
% 0.36/0.53          | ~ (l1_pre_topc @ X0)
% 0.36/0.53          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.53      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.53  thf('82', plain,
% 0.36/0.53      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.53  thf(t77_tops_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.53             ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.53               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.53  thf('83', plain,
% 0.36/0.53      (![X27 : $i, X28 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.53          | ~ (v4_pre_topc @ X27 @ X28)
% 0.36/0.54          | ((k2_tops_1 @ X28 @ X27)
% 0.36/0.54              = (k7_subset_1 @ (u1_struct_0 @ X28) @ X27 @ 
% 0.36/0.54                 (k1_tops_1 @ X28 @ X27)))
% 0.36/0.54          | ~ (l1_pre_topc @ X28)
% 0.36/0.54          | ~ (v2_pre_topc @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [t77_tops_1])).
% 0.36/0.54  thf('84', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v2_pre_topc @ X0)
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | ((k2_tops_1 @ X0 @ k1_xboole_0)
% 0.36/0.54              = (k7_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 0.36/0.54                 (k1_tops_1 @ X0 @ k1_xboole_0)))
% 0.36/0.54          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['82', '83'])).
% 0.36/0.54  thf('85', plain,
% 0.36/0.54      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.54  thf('86', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.36/0.54          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.54  thf('87', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 0.36/0.54           = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['85', '86'])).
% 0.36/0.54  thf(t36_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.54  thf('88', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.36/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.54  thf(t3_xboole_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.54  thf('89', plain,
% 0.36/0.54      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.54  thf('90', plain,
% 0.36/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['88', '89'])).
% 0.36/0.54  thf('91', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['87', '90'])).
% 0.36/0.54  thf('92', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v2_pre_topc @ X0)
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | ((k2_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.36/0.54          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['84', '91'])).
% 0.36/0.54  thf('93', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (v2_pre_topc @ X0)
% 0.36/0.54          | ((k2_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (v2_pre_topc @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['81', '92'])).
% 0.36/0.54  thf('94', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k2_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.36/0.54          | ~ (v2_pre_topc @ X0)
% 0.36/0.54          | ~ (l1_pre_topc @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['93'])).
% 0.36/0.54  thf('95', plain,
% 0.36/0.54      ((((k2_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | ~ (v2_pre_topc @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['76', '94'])).
% 0.36/0.54  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('98', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.36/0.54  thf('99', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.54  thf('100', plain, (((k1_xboole_0) = (sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '98', '99'])).
% 0.36/0.54  thf('101', plain, (((sk_B) != (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('102', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
