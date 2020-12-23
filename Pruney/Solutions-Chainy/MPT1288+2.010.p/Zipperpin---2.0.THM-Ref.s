%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5PZgd15P4L

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:59 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 267 expanded)
%              Number of leaves         :   32 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          : 1223 (3363 expanded)
%              Number of equality atoms :   32 ( 127 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t110_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t110_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tops_1 @ X24 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v2_tops_1 @ X26 @ X27 )
      | ~ ( v3_tops_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v2_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v2_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t95_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X29 @ X28 ) @ X29 )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t95_tops_1])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('25',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['20','21','22','28'])).

thf('30',plain,(
    v2_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['17','29'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ X18 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( k2_pre_topc @ X8 @ X7 ) @ ( k2_pre_topc @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ ( k1_tops_1 @ X20 @ X21 ) )
        = ( k1_tops_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['54','59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( k2_pre_topc @ X8 @ X7 ) @ ( k2_pre_topc @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_tops_1 @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_pre_topc @ X11 @ ( k1_tops_1 @ X11 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('81',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ ( k2_pre_topc @ X5 @ X6 ) )
        = ( k2_pre_topc @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('82',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','79','84'])).

thf('86',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','85'])).

thf('87',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('88',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ X18 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','94'])).

thf('96',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5PZgd15P4L
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.82/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.05  % Solved by: fo/fo7.sh
% 0.82/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.05  % done 924 iterations in 0.593s
% 0.82/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.05  % SZS output start Refutation
% 0.82/1.05  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.82/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.05  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.82/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.05  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.82/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.05  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.82/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.05  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.82/1.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.82/1.05  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.82/1.05  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.82/1.05  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.82/1.05  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.82/1.05  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.82/1.05  thf(t110_tops_1, conjecture,
% 0.82/1.05    (![A:$i]:
% 0.82/1.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.82/1.05       ( ![B:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05           ( ( v4_tops_1 @ B @ A ) =>
% 0.82/1.05             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.82/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.05    (~( ![A:$i]:
% 0.82/1.05        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.82/1.05          ( ![B:$i]:
% 0.82/1.05            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05              ( ( v4_tops_1 @ B @ A ) =>
% 0.82/1.05                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.82/1.05    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 0.82/1.05  thf('0', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf(dt_k1_tops_1, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ( l1_pre_topc @ A ) & 
% 0.82/1.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.05       ( m1_subset_1 @
% 0.82/1.05         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.82/1.05  thf('1', plain,
% 0.82/1.05      (![X12 : $i, X13 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ X12)
% 0.82/1.05          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.82/1.05          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.82/1.05             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.82/1.05      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.82/1.05  thf('2', plain,
% 0.82/1.05      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.82/1.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['0', '1'])).
% 0.82/1.05  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('4', plain,
% 0.82/1.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.05  thf(dt_k2_tops_1, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ( l1_pre_topc @ A ) & 
% 0.82/1.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.05       ( m1_subset_1 @
% 0.82/1.05         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.82/1.05  thf('5', plain,
% 0.82/1.05      (![X14 : $i, X15 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ X14)
% 0.82/1.05          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.82/1.05          | (m1_subset_1 @ (k2_tops_1 @ X14 @ X15) @ 
% 0.82/1.05             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.82/1.05      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.82/1.05  thf('6', plain,
% 0.82/1.05      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.82/1.05  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('8', plain,
% 0.82/1.05      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['6', '7'])).
% 0.82/1.05  thf(t84_tops_1, axiom,
% 0.82/1.05    (![A:$i]:
% 0.82/1.05     ( ( l1_pre_topc @ A ) =>
% 0.82/1.05       ( ![B:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05           ( ( v2_tops_1 @ B @ A ) <=>
% 0.82/1.05             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.82/1.05  thf('9', plain,
% 0.82/1.05      (![X24 : $i, X25 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.82/1.05          | ~ (v2_tops_1 @ X24 @ X25)
% 0.82/1.05          | ((k1_tops_1 @ X25 @ X24) = (k1_xboole_0))
% 0.82/1.05          | ~ (l1_pre_topc @ X25))),
% 0.82/1.05      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.82/1.05  thf('10', plain,
% 0.82/1.05      ((~ (l1_pre_topc @ sk_A)
% 0.82/1.05        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05            = (k1_xboole_0))
% 0.82/1.05        | ~ (v2_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['8', '9'])).
% 0.82/1.05  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('12', plain,
% 0.82/1.05      ((((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05          = (k1_xboole_0))
% 0.82/1.05        | ~ (v2_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.82/1.05      inference('demod', [status(thm)], ['10', '11'])).
% 0.82/1.05  thf('13', plain,
% 0.82/1.05      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['6', '7'])).
% 0.82/1.05  thf(t92_tops_1, axiom,
% 0.82/1.05    (![A:$i]:
% 0.82/1.05     ( ( l1_pre_topc @ A ) =>
% 0.82/1.05       ( ![B:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.82/1.05  thf('14', plain,
% 0.82/1.05      (![X26 : $i, X27 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.82/1.05          | (v2_tops_1 @ X26 @ X27)
% 0.82/1.05          | ~ (v3_tops_1 @ X26 @ X27)
% 0.82/1.05          | ~ (l1_pre_topc @ X27))),
% 0.82/1.05      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.82/1.05  thf('15', plain,
% 0.82/1.05      ((~ (l1_pre_topc @ sk_A)
% 0.82/1.05        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.82/1.05        | (v2_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['13', '14'])).
% 0.82/1.05  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('17', plain,
% 0.82/1.05      ((~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.82/1.05        | (v2_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.82/1.05      inference('demod', [status(thm)], ['15', '16'])).
% 0.82/1.05  thf('18', plain,
% 0.82/1.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.05  thf(t95_tops_1, axiom,
% 0.82/1.05    (![A:$i]:
% 0.82/1.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.82/1.05       ( ![B:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05           ( ( v3_pre_topc @ B @ A ) =>
% 0.82/1.05             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 0.82/1.05  thf('19', plain,
% 0.82/1.05      (![X28 : $i, X29 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.82/1.05          | (v3_tops_1 @ (k2_tops_1 @ X29 @ X28) @ X29)
% 0.82/1.05          | ~ (v3_pre_topc @ X28 @ X29)
% 0.82/1.05          | ~ (l1_pre_topc @ X29)
% 0.82/1.05          | ~ (v2_pre_topc @ X29))),
% 0.82/1.05      inference('cnf', [status(esa)], [t95_tops_1])).
% 0.82/1.05  thf('20', plain,
% 0.82/1.05      ((~ (v2_pre_topc @ sk_A)
% 0.82/1.05        | ~ (l1_pre_topc @ sk_A)
% 0.82/1.05        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.82/1.05        | (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['18', '19'])).
% 0.82/1.05  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('23', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf(fc9_tops_1, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.82/1.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.05       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.82/1.05  thf('24', plain,
% 0.82/1.05      (![X16 : $i, X17 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ X16)
% 0.82/1.05          | ~ (v2_pre_topc @ X16)
% 0.82/1.05          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.82/1.05          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 0.82/1.05      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.82/1.05  thf('25', plain,
% 0.82/1.05      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.82/1.05        | ~ (v2_pre_topc @ sk_A)
% 0.82/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['23', '24'])).
% 0.82/1.05  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('28', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.82/1.05      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.82/1.05  thf('29', plain,
% 0.82/1.05      ((v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.82/1.05      inference('demod', [status(thm)], ['20', '21', '22', '28'])).
% 0.82/1.05  thf('30', plain,
% 0.82/1.05      ((v2_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.82/1.05      inference('demod', [status(thm)], ['17', '29'])).
% 0.82/1.05  thf('31', plain,
% 0.82/1.05      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05         = (k1_xboole_0))),
% 0.82/1.05      inference('demod', [status(thm)], ['12', '30'])).
% 0.82/1.05  thf('32', plain,
% 0.82/1.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.05  thf(l78_tops_1, axiom,
% 0.82/1.05    (![A:$i]:
% 0.82/1.05     ( ( l1_pre_topc @ A ) =>
% 0.82/1.05       ( ![B:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05           ( ( k2_tops_1 @ A @ B ) =
% 0.82/1.05             ( k7_subset_1 @
% 0.82/1.05               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.82/1.05               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.82/1.05  thf('33', plain,
% 0.82/1.05      (![X18 : $i, X19 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.82/1.05          | ((k2_tops_1 @ X19 @ X18)
% 0.82/1.05              = (k7_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.82/1.05                 (k2_pre_topc @ X19 @ X18) @ (k1_tops_1 @ X19 @ X18)))
% 0.82/1.05          | ~ (l1_pre_topc @ X19))),
% 0.82/1.05      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.82/1.05  thf('34', plain,
% 0.82/1.05      ((~ (l1_pre_topc @ sk_A)
% 0.82/1.05        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.82/1.05            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.05               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.82/1.05      inference('sup-', [status(thm)], ['32', '33'])).
% 0.82/1.05  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('36', plain,
% 0.82/1.05      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.82/1.05         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.05            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05            (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.82/1.05      inference('demod', [status(thm)], ['34', '35'])).
% 0.82/1.05  thf('37', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('38', plain,
% 0.82/1.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.05  thf('39', plain,
% 0.82/1.05      (![X12 : $i, X13 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ X12)
% 0.82/1.05          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.82/1.05          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.82/1.05             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.82/1.05      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.82/1.05  thf('40', plain,
% 0.82/1.05      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['38', '39'])).
% 0.82/1.05  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('42', plain,
% 0.82/1.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['40', '41'])).
% 0.82/1.05  thf(t49_pre_topc, axiom,
% 0.82/1.05    (![A:$i]:
% 0.82/1.05     ( ( l1_pre_topc @ A ) =>
% 0.82/1.05       ( ![B:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05           ( ![C:$i]:
% 0.82/1.05             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05               ( ( r1_tarski @ B @ C ) =>
% 0.82/1.05                 ( r1_tarski @
% 0.82/1.05                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.82/1.05  thf('43', plain,
% 0.82/1.05      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.82/1.05          | ~ (r1_tarski @ X7 @ X9)
% 0.82/1.05          | (r1_tarski @ (k2_pre_topc @ X8 @ X7) @ (k2_pre_topc @ X8 @ X9))
% 0.82/1.05          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.82/1.05          | ~ (l1_pre_topc @ X8))),
% 0.82/1.05      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.82/1.05  thf('44', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ sk_A)
% 0.82/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05          | (r1_tarski @ 
% 0.82/1.05             (k2_pre_topc @ sk_A @ 
% 0.82/1.05              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.82/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.82/1.05          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.82/1.05      inference('sup-', [status(thm)], ['42', '43'])).
% 0.82/1.05  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('46', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05          | (r1_tarski @ 
% 0.82/1.05             (k2_pre_topc @ sk_A @ 
% 0.82/1.05              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.82/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.82/1.05          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.82/1.05      inference('demod', [status(thm)], ['44', '45'])).
% 0.82/1.05  thf('47', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf(projectivity_k1_tops_1, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ( l1_pre_topc @ A ) & 
% 0.82/1.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.05       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.82/1.05  thf('48', plain,
% 0.82/1.05      (![X20 : $i, X21 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ X20)
% 0.82/1.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.82/1.05          | ((k1_tops_1 @ X20 @ (k1_tops_1 @ X20 @ X21))
% 0.82/1.05              = (k1_tops_1 @ X20 @ X21)))),
% 0.82/1.05      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.82/1.05  thf('49', plain,
% 0.82/1.05      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.82/1.05          = (k1_tops_1 @ sk_A @ sk_B))
% 0.82/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['47', '48'])).
% 0.82/1.05  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('51', plain,
% 0.82/1.05      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.82/1.05         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.82/1.05      inference('demod', [status(thm)], ['49', '50'])).
% 0.82/1.05  thf('52', plain,
% 0.82/1.05      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.82/1.05         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.82/1.05      inference('demod', [status(thm)], ['49', '50'])).
% 0.82/1.05  thf('53', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.82/1.05          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.82/1.05      inference('demod', [status(thm)], ['46', '51', '52'])).
% 0.82/1.05  thf('54', plain,
% 0.82/1.05      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.82/1.05        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05           (k2_pre_topc @ sk_A @ sk_B)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['37', '53'])).
% 0.82/1.05  thf('55', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf(t44_tops_1, axiom,
% 0.82/1.05    (![A:$i]:
% 0.82/1.05     ( ( l1_pre_topc @ A ) =>
% 0.82/1.05       ( ![B:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.82/1.05  thf('56', plain,
% 0.82/1.05      (![X22 : $i, X23 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.82/1.05          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 0.82/1.05          | ~ (l1_pre_topc @ X23))),
% 0.82/1.05      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.82/1.05  thf('57', plain,
% 0.82/1.05      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.82/1.05      inference('sup-', [status(thm)], ['55', '56'])).
% 0.82/1.05  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('59', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.82/1.05      inference('demod', [status(thm)], ['57', '58'])).
% 0.82/1.05  thf('60', plain,
% 0.82/1.05      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05        (k2_pre_topc @ sk_A @ sk_B))),
% 0.82/1.05      inference('demod', [status(thm)], ['54', '59'])).
% 0.82/1.05  thf(d10_xboole_0, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.82/1.05  thf('61', plain,
% 0.82/1.05      (![X0 : $i, X2 : $i]:
% 0.82/1.05         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.82/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.82/1.05  thf('62', plain,
% 0.82/1.05      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.82/1.05           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.82/1.05            = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.82/1.05      inference('sup-', [status(thm)], ['60', '61'])).
% 0.82/1.05  thf('63', plain,
% 0.82/1.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.05  thf(dt_k2_pre_topc, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ( l1_pre_topc @ A ) & 
% 0.82/1.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.05       ( m1_subset_1 @
% 0.82/1.05         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.82/1.05  thf('64', plain,
% 0.82/1.05      (![X3 : $i, X4 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ X3)
% 0.82/1.05          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.82/1.05          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.82/1.05             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.82/1.05      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.82/1.05  thf('65', plain,
% 0.82/1.05      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['63', '64'])).
% 0.82/1.05  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('67', plain,
% 0.82/1.05      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['65', '66'])).
% 0.82/1.05  thf('68', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('69', plain,
% 0.82/1.05      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.82/1.05          | ~ (r1_tarski @ X7 @ X9)
% 0.82/1.05          | (r1_tarski @ (k2_pre_topc @ X8 @ X7) @ (k2_pre_topc @ X8 @ X9))
% 0.82/1.05          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.82/1.05          | ~ (l1_pre_topc @ X8))),
% 0.82/1.05      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.82/1.05  thf('70', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ sk_A)
% 0.82/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.82/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.82/1.05          | ~ (r1_tarski @ sk_B @ X0))),
% 0.82/1.05      inference('sup-', [status(thm)], ['68', '69'])).
% 0.82/1.05  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('72', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.82/1.05          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.82/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.82/1.05          | ~ (r1_tarski @ sk_B @ X0))),
% 0.82/1.05      inference('demod', [status(thm)], ['70', '71'])).
% 0.82/1.05  thf('73', plain,
% 0.82/1.05      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.82/1.05           (k2_pre_topc @ sk_A @ 
% 0.82/1.05            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.82/1.05      inference('sup-', [status(thm)], ['67', '72'])).
% 0.82/1.05  thf('74', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf(d6_tops_1, axiom,
% 0.82/1.05    (![A:$i]:
% 0.82/1.05     ( ( l1_pre_topc @ A ) =>
% 0.82/1.05       ( ![B:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/1.05           ( ( v4_tops_1 @ B @ A ) <=>
% 0.82/1.05             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.82/1.05               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.82/1.05  thf('75', plain,
% 0.82/1.05      (![X10 : $i, X11 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.82/1.05          | ~ (v4_tops_1 @ X10 @ X11)
% 0.82/1.05          | (r1_tarski @ X10 @ (k2_pre_topc @ X11 @ (k1_tops_1 @ X11 @ X10)))
% 0.82/1.05          | ~ (l1_pre_topc @ X11))),
% 0.82/1.05      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.82/1.05  thf('76', plain,
% 0.82/1.05      ((~ (l1_pre_topc @ sk_A)
% 0.82/1.05        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['74', '75'])).
% 0.82/1.05  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('78', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('79', plain,
% 0.82/1.05      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.82/1.05  thf('80', plain,
% 0.82/1.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.82/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.05  thf(projectivity_k2_pre_topc, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ( l1_pre_topc @ A ) & 
% 0.82/1.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.05       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.82/1.05         ( k2_pre_topc @ A @ B ) ) ))).
% 0.82/1.05  thf('81', plain,
% 0.82/1.05      (![X5 : $i, X6 : $i]:
% 0.82/1.05         (~ (l1_pre_topc @ X5)
% 0.82/1.05          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.82/1.05          | ((k2_pre_topc @ X5 @ (k2_pre_topc @ X5 @ X6))
% 0.82/1.05              = (k2_pre_topc @ X5 @ X6)))),
% 0.82/1.05      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.82/1.05  thf('82', plain,
% 0.82/1.05      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.82/1.05      inference('sup-', [status(thm)], ['80', '81'])).
% 0.82/1.05  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('84', plain,
% 0.82/1.05      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.82/1.05         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('demod', [status(thm)], ['82', '83'])).
% 0.82/1.05  thf('85', plain,
% 0.82/1.05      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.82/1.05        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('demod', [status(thm)], ['73', '79', '84'])).
% 0.82/1.05  thf('86', plain,
% 0.82/1.05      (((k2_pre_topc @ sk_A @ sk_B)
% 0.82/1.05         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('demod', [status(thm)], ['62', '85'])).
% 0.82/1.05  thf('87', plain,
% 0.82/1.05      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.82/1.05         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.82/1.05      inference('demod', [status(thm)], ['49', '50'])).
% 0.82/1.05  thf('88', plain,
% 0.82/1.05      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.82/1.05         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.82/1.05            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('demod', [status(thm)], ['36', '86', '87'])).
% 0.82/1.05  thf('89', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('90', plain,
% 0.82/1.05      (![X18 : $i, X19 : $i]:
% 0.82/1.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.82/1.05          | ((k2_tops_1 @ X19 @ X18)
% 0.82/1.05              = (k7_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.82/1.05                 (k2_pre_topc @ X19 @ X18) @ (k1_tops_1 @ X19 @ X18)))
% 0.82/1.05          | ~ (l1_pre_topc @ X19))),
% 0.82/1.05      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.82/1.05  thf('91', plain,
% 0.82/1.05      ((~ (l1_pre_topc @ sk_A)
% 0.82/1.05        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.82/1.05            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.05               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.82/1.05      inference('sup-', [status(thm)], ['89', '90'])).
% 0.82/1.05  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('93', plain,
% 0.82/1.05      (((k2_tops_1 @ sk_A @ sk_B)
% 0.82/1.05         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.82/1.05            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('demod', [status(thm)], ['91', '92'])).
% 0.82/1.05  thf('94', plain,
% 0.82/1.05      (((k2_tops_1 @ sk_A @ sk_B)
% 0.82/1.05         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('sup+', [status(thm)], ['88', '93'])).
% 0.82/1.05  thf('95', plain,
% 0.82/1.05      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.82/1.05      inference('demod', [status(thm)], ['31', '94'])).
% 0.82/1.05  thf('96', plain,
% 0.82/1.05      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('97', plain, ($false),
% 0.82/1.05      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.82/1.05  
% 0.82/1.05  % SZS output end Refutation
% 0.82/1.05  
% 0.82/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
