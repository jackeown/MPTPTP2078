%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eDVoarN4OW

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:40 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 320 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  790 (3653 expanded)
%              Number of equality atoms :   39 ( 178 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tops_1 @ X28 @ X29 )
      | ( r1_tarski @ X28 @ ( k2_tops_1 @ X29 @ X28 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(fc13_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_tops_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v1_xboole_0 @ ( k1_tops_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_tops_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_tops_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tops_1 @ X26 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_tops_1 @ X18 @ X19 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X19 @ X18 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','28'])).

thf('30',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_pre_topc @ X25 @ ( k1_tops_1 @ X25 @ ( k2_pre_topc @ X25 @ X24 ) ) )
        = ( k2_pre_topc @ X25 @ X24 ) )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t59_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_tops_1 @ X23 @ X22 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k2_pre_topc @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tops_1 @ X26 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('49',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v2_tops_1 @ X30 @ X31 )
      | ~ ( v3_tops_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( ( k7_subset_1 @ X3 @ X2 @ X4 )
        = ( k4_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','54','57','58'])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','24'])).

thf('61',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','54','57','58'])).

thf('62',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','54','57','58'])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','59','62','63'])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['34','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( k1_xboole_0
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('70',plain,(
    r1_tarski @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3','68','69'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('71',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('72',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eDVoarN4OW
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 145 iterations in 0.117s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.59  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.40/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.59  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.40/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.40/0.59  thf(t97_tops_1, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.40/0.59             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.40/0.59                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t88_tops_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( v2_tops_1 @ B @ A ) <=>
% 0.40/0.59             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X28 : $i, X29 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.40/0.59          | ~ (v2_tops_1 @ X28 @ X29)
% 0.40/0.59          | (r1_tarski @ X28 @ (k2_tops_1 @ X29 @ X28))
% 0.40/0.59          | ~ (l1_pre_topc @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.59        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t4_subset_1, axiom,
% 0.40/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.59  thf(cc2_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.59          | (v4_pre_topc @ X12 @ X13)
% 0.40/0.59          | ~ (v1_xboole_0 @ X12)
% 0.40/0.59          | ~ (l1_pre_topc @ X13)
% 0.40/0.59          | ~ (v2_pre_topc @ X13))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.59          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_k2_pre_topc, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( l1_pre_topc @ A ) & 
% 0.40/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.59       ( m1_subset_1 @
% 0.40/0.59         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X14)
% 0.40/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.40/0.59          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.59  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf(fc13_tops_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( l1_pre_topc @ A ) & ( v2_tops_1 @ B @ A ) & 
% 0.40/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.59       ( v1_xboole_0 @ ( k1_tops_1 @ A @ B ) ) ))).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X20)
% 0.40/0.59          | ~ (v2_tops_1 @ X21 @ X20)
% 0.40/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.40/0.59          | (v1_xboole_0 @ (k1_tops_1 @ X20 @ X21)))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc13_tops_1])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.40/0.59        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf(t84_tops_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( v2_tops_1 @ B @ A ) <=>
% 0.40/0.59             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X26 : $i, X27 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.40/0.59          | ~ (v2_tops_1 @ X26 @ X27)
% 0.40/0.59          | ((k1_tops_1 @ X27 @ X26) = (k1_xboole_0))
% 0.40/0.59          | ~ (l1_pre_topc @ X27))),
% 0.40/0.59      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.40/0.59        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      ((((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.40/0.59        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d5_tops_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( v3_tops_1 @ B @ A ) <=>
% 0.40/0.59             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.40/0.59          | ~ (v3_tops_1 @ X18 @ X19)
% 0.40/0.59          | (v2_tops_1 @ (k2_pre_topc @ X19 @ X18) @ X19)
% 0.40/0.59          | ~ (l1_pre_topc @ X19))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.40/0.59        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('23', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('24', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['18', '24'])).
% 0.40/0.59  thf('26', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.40/0.59  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.59      inference('demod', [status(thm)], ['13', '25', '26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['6', '28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.59  thf(t52_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.40/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.40/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.40/0.59          | ~ (v4_pre_topc @ X16 @ X17)
% 0.40/0.59          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.40/0.59          | ~ (l1_pre_topc @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X0)
% 0.40/0.59          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.59          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.59          | ~ (l1_pre_topc @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '32'])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['33'])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t59_tops_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( v3_pre_topc @ B @ A ) =>
% 0.40/0.59             ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) =
% 0.40/0.59               ( k2_pre_topc @ A @ B ) ) ) ) ) ))).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      (![X24 : $i, X25 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.40/0.59          | ((k2_pre_topc @ X25 @ (k1_tops_1 @ X25 @ (k2_pre_topc @ X25 @ X24)))
% 0.40/0.59              = (k2_pre_topc @ X25 @ X24))
% 0.40/0.59          | ~ (v3_pre_topc @ X24 @ X25)
% 0.40/0.59          | ~ (l1_pre_topc @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [t59_tops_1])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.40/0.59        | ((k2_pre_topc @ sk_A @ 
% 0.40/0.59            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.40/0.59            = (k2_pre_topc @ sk_A @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('39', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(l78_tops_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.59             ( k7_subset_1 @
% 0.40/0.59               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.40/0.59               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.40/0.59          | ((k2_tops_1 @ X23 @ X22)
% 0.40/0.59              = (k7_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.40/0.59                 (k2_pre_topc @ X23 @ X22) @ (k1_tops_1 @ X23 @ X22)))
% 0.40/0.59          | ~ (l1_pre_topc @ X23))),
% 0.40/0.59      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.59            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X26 : $i, X27 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.40/0.59          | ~ (v2_tops_1 @ X26 @ X27)
% 0.40/0.59          | ((k1_tops_1 @ X27 @ X26) = (k1_xboole_0))
% 0.40/0.59          | ~ (l1_pre_topc @ X27))),
% 0.40/0.59      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.40/0.59        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.59  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t92_tops_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (![X30 : $i, X31 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.40/0.59          | (v2_tops_1 @ X30 @ X31)
% 0.40/0.59          | ~ (v3_tops_1 @ X30 @ X31)
% 0.40/0.59          | ~ (l1_pre_topc @ X31))),
% 0.40/0.59      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.40/0.59        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.40/0.59  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('52', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('53', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.40/0.59  thf('54', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['46', '47', '53'])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf(redefinition_k7_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.40/0.59          | ((k7_subset_1 @ X3 @ X2 @ X4) = (k4_xboole_0 @ X2 @ X4)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.59           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.59  thf(t3_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.59  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf('59', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43', '54', '57', '58'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['18', '24'])).
% 0.40/0.59  thf('61', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43', '54', '57', '58'])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['60', '61'])).
% 0.40/0.59  thf('63', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43', '54', '57', '58'])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k2_tops_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['37', '38', '39', '59', '62', '63'])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      ((((k1_xboole_0) = (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ~ (v2_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup+', [status(thm)], ['34', '64'])).
% 0.40/0.59  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('68', plain, (((k1_xboole_0) = (k2_tops_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.40/0.59  thf('69', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.40/0.59  thf('70', plain, ((r1_tarski @ sk_B @ k1_xboole_0)),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '3', '68', '69'])).
% 0.40/0.59  thf(t3_xboole_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.59  thf('71', plain,
% 0.40/0.59      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.40/0.59  thf('72', plain, (((sk_B) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.40/0.59  thf('73', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('74', plain, ($false),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
