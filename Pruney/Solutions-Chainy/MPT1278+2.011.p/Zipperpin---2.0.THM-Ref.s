%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qk5PzojgpF

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:41 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 556 expanded)
%              Number of leaves         :   38 ( 190 expanded)
%              Depth                    :   15
%              Number of atoms          : 1255 (4915 expanded)
%              Number of equality atoms :   82 ( 370 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tops_1 @ X18 @ X19 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v2_tops_1 @ X32 @ X33 )
      | ~ ( v3_tops_1 @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25','31'])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','32'])).

thf('34',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ( v4_pre_topc @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf('40',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ ( k1_tops_1 @ X22 @ X23 ) )
        = ( k1_tops_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tops_1 @ X28 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X28 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','52','53','54'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('57',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('58',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X29 @ X28 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('67',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X3 @ X4 ) )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X3 @ X4 ) )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('71',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','75','76'])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tops_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v2_tops_1 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tops_1 @ X18 @ X19 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( v2_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('87',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('88',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','92','93'])).

thf('95',plain,
    ( ( v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('99',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('103',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('104',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v3_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('110',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ( v4_pre_topc @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('113',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','118'])).

thf('120',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['108','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('124',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('132',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['43','130','131'])).

thf('133',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qk5PzojgpF
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 354 iterations in 0.139s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.42/0.62  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.42/0.62  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.42/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.42/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.42/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.42/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.42/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.42/0.62  thf(t97_tops_1, conjecture,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.42/0.62             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i]:
% 0.42/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62          ( ![B:$i]:
% 0.42/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.42/0.62                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(involutiveness_k3_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.42/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.42/0.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d5_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X7 : $i, X8 : $i]:
% 0.42/0.62         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.42/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.42/0.62         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['2', '5'])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_k3_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 0.42/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.42/0.62         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf(t52_pre_topc, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.42/0.62             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.42/0.62               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.42/0.62          | ~ (v4_pre_topc @ X14 @ X15)
% 0.42/0.62          | ((k2_pre_topc @ X15 @ X14) = (X14))
% 0.42/0.62          | ~ (l1_pre_topc @ X15))),
% 0.42/0.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.42/0.62            = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.42/0.62        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.42/0.62          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.42/0.62        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf(d3_tops_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( v1_tops_1 @ B @ A ) <=>
% 0.42/0.62             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X16 : $i, X17 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.42/0.62          | ~ (v1_tops_1 @ X16 @ X17)
% 0.42/0.62          | ((k2_pre_topc @ X17 @ X16) = (k2_struct_0 @ X17))
% 0.42/0.62          | ~ (l1_pre_topc @ X17))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.42/0.62            = (k2_struct_0 @ sk_A))
% 0.42/0.62        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.62  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.42/0.62          = (k2_struct_0 @ sk_A))
% 0.42/0.62        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d4_tops_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( v2_tops_1 @ B @ A ) <=>
% 0.42/0.62             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.42/0.62          | ~ (v2_tops_1 @ X18 @ X19)
% 0.42/0.62          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18) @ X19)
% 0.42/0.62          | ~ (l1_pre_topc @ X19))),
% 0.42/0.62      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.42/0.62        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.62  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.42/0.62         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t92_tops_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X32 : $i, X33 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.42/0.62          | (v2_tops_1 @ X32 @ X33)
% 0.42/0.62          | ~ (v3_tops_1 @ X32 @ X33)
% 0.42/0.62          | ~ (l1_pre_topc @ X33))),
% 0.42/0.62      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.42/0.62        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('30', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('31', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      ((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['23', '24', '25', '31'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.42/0.62         = (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['20', '32'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      ((((k2_struct_0 @ sk_A) = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.42/0.62        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['15', '33'])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf(t29_tops_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( v4_pre_topc @ B @ A ) <=>
% 0.42/0.62             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.42/0.62          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 0.42/0.62          | (v4_pre_topc @ X24 @ X25)
% 0.42/0.62          | ~ (l1_pre_topc @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.42/0.62        | ~ (v3_pre_topc @ 
% 0.42/0.62             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.42/0.62             sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.62  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['2', '5'])).
% 0.42/0.62  thf('40', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (((k2_struct_0 @ sk_A) = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['34', '41'])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['6', '42'])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(projectivity_k1_tops_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.42/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.62       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (![X22 : $i, X23 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X22)
% 0.42/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.42/0.62          | ((k1_tops_1 @ X22 @ (k1_tops_1 @ X22 @ X23))
% 0.42/0.62              = (k1_tops_1 @ X22 @ X23)))),
% 0.42/0.62      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.42/0.62          = (k1_tops_1 @ sk_A @ sk_B))
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t84_tops_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( v2_tops_1 @ B @ A ) <=>
% 0.42/0.62             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (![X28 : $i, X29 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.42/0.62          | ~ (v2_tops_1 @ X28 @ X29)
% 0.42/0.62          | ((k1_tops_1 @ X29 @ X28) = (k1_xboole_0))
% 0.42/0.62          | ~ (l1_pre_topc @ X29))),
% 0.42/0.62      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.62        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('51', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.42/0.62  thf('52', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.42/0.62  thf('53', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.42/0.62  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('55', plain, (((k1_tops_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['46', '52', '53', '54'])).
% 0.42/0.62  thf(dt_k2_subset_1, axiom,
% 0.42/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.42/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.42/0.62  thf('57', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.42/0.62  thf('58', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.42/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 0.42/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.42/0.62  thf('61', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.42/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      (![X7 : $i, X8 : $i]:
% 0.42/0.62         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.42/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['60', '63'])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      (![X28 : $i, X29 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.42/0.62          | ((k1_tops_1 @ X29 @ X28) != (k1_xboole_0))
% 0.42/0.62          | (v2_tops_1 @ X28 @ X29)
% 0.42/0.62          | ~ (l1_pre_topc @ X29))),
% 0.42/0.62      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.42/0.62  thf('66', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X0)
% 0.42/0.62          | (v2_tops_1 @ 
% 0.42/0.62             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.42/0.62          | ((k1_tops_1 @ X0 @ 
% 0.42/0.62              (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.42/0.62              != (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.62  thf(t3_boole, axiom,
% 0.42/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.62  thf('67', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.42/0.62  thf(t48_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.62  thf('68', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i]:
% 0.42/0.62         ((k4_xboole_0 @ X3 @ (k4_xboole_0 @ X3 @ X4))
% 0.42/0.62           = (k3_xboole_0 @ X3 @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['67', '68'])).
% 0.42/0.62  thf('70', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i]:
% 0.42/0.62         ((k4_xboole_0 @ X3 @ (k4_xboole_0 @ X3 @ X4))
% 0.42/0.62           = (k3_xboole_0 @ X3 @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.62  thf(t4_boole, axiom,
% 0.42/0.62    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.42/0.62  thf('71', plain,
% 0.42/0.62      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t4_boole])).
% 0.42/0.62  thf('72', plain,
% 0.42/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['70', '71'])).
% 0.42/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.62  thf('73', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.62  thf('74', plain,
% 0.42/0.62      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['72', '73'])).
% 0.42/0.62  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['69', '74'])).
% 0.42/0.62  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['69', '74'])).
% 0.42/0.62  thf('77', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X0)
% 0.42/0.62          | (v2_tops_1 @ k1_xboole_0 @ X0)
% 0.42/0.62          | ((k1_tops_1 @ X0 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['66', '75', '76'])).
% 0.42/0.62  thf('78', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62        | (v2_tops_1 @ k1_xboole_0 @ sk_A)
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['55', '77'])).
% 0.42/0.62  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('80', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ k1_xboole_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.42/0.62  thf('81', plain, ((v2_tops_1 @ k1_xboole_0 @ sk_A)),
% 0.42/0.62      inference('simplify', [status(thm)], ['80'])).
% 0.42/0.62  thf('82', plain,
% 0.42/0.62      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['60', '63'])).
% 0.42/0.62  thf('83', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.42/0.62          | ~ (v2_tops_1 @ X18 @ X19)
% 0.42/0.62          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18) @ X19)
% 0.42/0.62          | ~ (l1_pre_topc @ X19))),
% 0.42/0.62      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.42/0.62  thf('84', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X0)
% 0.42/0.62          | (v1_tops_1 @ 
% 0.42/0.62             (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.42/0.62              (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))) @ 
% 0.42/0.62             X0)
% 0.42/0.62          | ~ (v2_tops_1 @ 
% 0.42/0.62               (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('85', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['69', '74'])).
% 0.42/0.62  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['69', '74'])).
% 0.42/0.62  thf('87', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.42/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('88', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.42/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.42/0.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.42/0.62  thf('89', plain,
% 0.42/0.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.42/0.62  thf('90', plain,
% 0.42/0.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.42/0.62  thf('91', plain,
% 0.42/0.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['89', '90'])).
% 0.42/0.62  thf('92', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['86', '91'])).
% 0.42/0.62  thf('93', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['69', '74'])).
% 0.42/0.62  thf('94', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X0)
% 0.42/0.62          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.42/0.62          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['84', '85', '92', '93'])).
% 0.42/0.62  thf('95', plain,
% 0.42/0.62      (((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['81', '94'])).
% 0.42/0.62  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('97', plain, ((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['95', '96'])).
% 0.42/0.62  thf('98', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.42/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('99', plain,
% 0.42/0.62      (![X16 : $i, X17 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.42/0.62          | ~ (v1_tops_1 @ X16 @ X17)
% 0.42/0.62          | ((k2_pre_topc @ X17 @ X16) = (k2_struct_0 @ X17))
% 0.42/0.62          | ~ (l1_pre_topc @ X17))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.42/0.62  thf('100', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X0)
% 0.42/0.62          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.42/0.62          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['98', '99'])).
% 0.42/0.62  thf('101', plain,
% 0.42/0.62      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['97', '100'])).
% 0.42/0.62  thf('102', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(fc9_tops_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.42/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.62       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.42/0.62  thf('103', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X20)
% 0.42/0.62          | ~ (v2_pre_topc @ X20)
% 0.42/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.42/0.62          | (v3_pre_topc @ (k1_tops_1 @ X20 @ X21) @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.42/0.62  thf('104', plain,
% 0.42/0.62      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.42/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['102', '103'])).
% 0.42/0.62  thf('105', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.42/0.62  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('108', plain, ((v3_pre_topc @ k1_xboole_0 @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.42/0.62  thf('109', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.42/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('110', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.42/0.62          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 0.42/0.62          | (v4_pre_topc @ X24 @ X25)
% 0.42/0.62          | ~ (l1_pre_topc @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.42/0.62  thf('111', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X0)
% 0.42/0.62          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.42/0.62          | ~ (v3_pre_topc @ 
% 0.42/0.62               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['109', '110'])).
% 0.42/0.62  thf('112', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['69', '74'])).
% 0.42/0.62  thf('113', plain,
% 0.42/0.62      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['60', '63'])).
% 0.42/0.62  thf('114', plain,
% 0.42/0.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['112', '113'])).
% 0.42/0.62  thf('115', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.42/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.42/0.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.42/0.62  thf('116', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.42/0.62  thf('117', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['86', '91'])).
% 0.42/0.62  thf('118', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['116', '117'])).
% 0.42/0.62  thf('119', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X0)
% 0.42/0.62          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.42/0.62          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['111', '118'])).
% 0.42/0.62  thf('120', plain,
% 0.42/0.62      (((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['108', '119'])).
% 0.42/0.62  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('122', plain, ((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['120', '121'])).
% 0.42/0.62  thf('123', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.42/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('124', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.42/0.62          | ~ (v4_pre_topc @ X14 @ X15)
% 0.42/0.62          | ((k2_pre_topc @ X15 @ X14) = (X14))
% 0.42/0.62          | ~ (l1_pre_topc @ X15))),
% 0.42/0.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.42/0.62  thf('125', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X0)
% 0.42/0.62          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.42/0.62          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['123', '124'])).
% 0.42/0.62  thf('126', plain,
% 0.42/0.62      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['122', '125'])).
% 0.42/0.62  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('128', plain,
% 0.42/0.62      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['126', '127'])).
% 0.42/0.62  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('130', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['101', '128', '129'])).
% 0.42/0.62  thf('131', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['116', '117'])).
% 0.42/0.62  thf('132', plain, (((k1_xboole_0) = (sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['43', '130', '131'])).
% 0.42/0.62  thf('133', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('134', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
