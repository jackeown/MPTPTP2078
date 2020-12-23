%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xLNyBrEHOp

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:13 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 355 expanded)
%              Number of leaves         :   26 ( 121 expanded)
%              Depth                    :   16
%              Number of atoms          :  790 (3682 expanded)
%              Number of equality atoms :   24 (  96 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_tops_1 @ X32 @ X31 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k2_pre_topc @ X32 @ X31 ) @ ( k2_pre_topc @ X32 @ ( k3_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 ) ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ( r1_tarski @ ( k3_subset_1 @ X17 @ X16 ) @ ( k3_subset_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X17 @ X16 ) @ ( k3_subset_1 @ X17 @ X18 ) )
      | ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','37'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X20 @ X21 ) @ ( k3_subset_1 @ X20 @ ( k9_subset_1 @ X20 @ X21 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('57',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf('58',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('59',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['50','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xLNyBrEHOp
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 696 iterations in 0.426s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.69/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.69/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.88  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.69/0.88  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.69/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.88  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.88  thf(t69_tops_1, conjecture,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( l1_pre_topc @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.88           ( ( v4_pre_topc @ B @ A ) =>
% 0.69/0.88             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i]:
% 0.69/0.88        ( ( l1_pre_topc @ A ) =>
% 0.69/0.88          ( ![B:$i]:
% 0.69/0.88            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.88              ( ( v4_pre_topc @ B @ A ) =>
% 0.69/0.88                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(d2_tops_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( l1_pre_topc @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.88           ( ( k2_tops_1 @ A @ B ) =
% 0.69/0.88             ( k9_subset_1 @
% 0.69/0.88               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.69/0.88               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.69/0.88  thf('1', plain,
% 0.69/0.88      (![X31 : $i, X32 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.69/0.88          | ((k2_tops_1 @ X32 @ X31)
% 0.69/0.88              = (k9_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.69/0.88                 (k2_pre_topc @ X32 @ X31) @ 
% 0.69/0.88                 (k2_pre_topc @ X32 @ (k3_subset_1 @ (u1_struct_0 @ X32) @ X31))))
% 0.69/0.88          | ~ (l1_pre_topc @ X32))),
% 0.69/0.88      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.88        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.88            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.88               (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.69/0.88               (k2_pre_topc @ sk_A @ 
% 0.69/0.88                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.88  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('4', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t52_pre_topc, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( l1_pre_topc @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.88           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.69/0.88             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.69/0.88               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      (![X29 : $i, X30 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.88          | ~ (v4_pre_topc @ X29 @ X30)
% 0.69/0.88          | ((k2_pre_topc @ X30 @ X29) = (X29))
% 0.69/0.88          | ~ (l1_pre_topc @ X30))),
% 0.69/0.88      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.88        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.69/0.88        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['4', '5'])).
% 0.69/0.88  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.69/0.88      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.69/0.88  thf('10', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(d5_subset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.88       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.69/0.88  thf('11', plain,
% 0.69/0.88      (![X11 : $i, X12 : $i]:
% 0.69/0.88         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.69/0.88          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.69/0.88  thf('12', plain,
% 0.69/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.69/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.88         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.88            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.69/0.88      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 0.69/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.69/0.88  thf('14', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.69/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.88  thf(t3_subset, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.88  thf('15', plain,
% 0.69/0.88      (![X24 : $i, X26 : $i]:
% 0.69/0.88         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.69/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t31_subset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.88       ( ![C:$i]:
% 0.69/0.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.88           ( ( r1_tarski @ B @ C ) <=>
% 0.69/0.88             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.69/0.88          | ~ (r1_tarski @ X18 @ X16)
% 0.69/0.88          | (r1_tarski @ (k3_subset_1 @ X17 @ X16) @ (k3_subset_1 @ X17 @ X18))
% 0.69/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.88          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.69/0.88          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['17', '18'])).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.69/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.88          | (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.69/0.88          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.69/0.88      inference('demod', [status(thm)], ['19', '20'])).
% 0.69/0.88  thf('22', plain,
% 0.69/0.88      ((~ (r1_tarski @ k1_xboole_0 @ sk_B)
% 0.69/0.88        | (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['16', '21'])).
% 0.69/0.88  thf('23', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.69/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      (![X11 : $i, X12 : $i]:
% 0.69/0.88         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.69/0.88          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.69/0.88  thf('26', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.88  thf(t3_boole, axiom,
% 0.69/0.88    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.88  thf('27', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.69/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.88  thf('28', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('29', plain,
% 0.69/0.88      ((r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88        (u1_struct_0 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.69/0.88  thf('30', plain,
% 0.69/0.88      (![X24 : $i, X26 : $i]:
% 0.69/0.88         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.69/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.88  thf(dt_k2_pre_topc, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( l1_pre_topc @ A ) & 
% 0.69/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.88       ( m1_subset_1 @
% 0.69/0.88         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      (![X27 : $i, X28 : $i]:
% 0.69/0.88         (~ (l1_pre_topc @ X27)
% 0.69/0.88          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.69/0.88          | (m1_subset_1 @ (k2_pre_topc @ X27 @ X28) @ 
% 0.69/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.69/0.88  thf('33', plain,
% 0.69/0.88      (((m1_subset_1 @ 
% 0.69/0.88         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.69/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['31', '32'])).
% 0.69/0.88  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('35', plain,
% 0.69/0.88      ((m1_subset_1 @ 
% 0.69/0.88        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['33', '34'])).
% 0.69/0.88  thf(dt_k9_subset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.88       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.88  thf('36', plain,
% 0.69/0.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.88         ((m1_subset_1 @ (k9_subset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X13))
% 0.69/0.88          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.69/0.88  thf('37', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (m1_subset_1 @ 
% 0.69/0.88          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.69/0.88           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.69/0.88          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['35', '36'])).
% 0.69/0.88  thf('38', plain,
% 0.69/0.88      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['13', '37'])).
% 0.69/0.88  thf('39', plain,
% 0.69/0.88      (![X11 : $i, X12 : $i]:
% 0.69/0.88         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.69/0.88          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.69/0.88  thf('40', plain,
% 0.69/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['38', '39'])).
% 0.69/0.88  thf('41', plain,
% 0.69/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.69/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('42', plain,
% 0.69/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.69/0.88          | ~ (r1_tarski @ (k3_subset_1 @ X17 @ X16) @ 
% 0.69/0.88               (k3_subset_1 @ X17 @ X18))
% 0.69/0.88          | (r1_tarski @ X18 @ X16)
% 0.69/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.69/0.88  thf('43', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.88          | (r1_tarski @ X0 @ sk_B)
% 0.69/0.88          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['41', '42'])).
% 0.69/0.88  thf('44', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('45', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.88          | (r1_tarski @ X0 @ sk_B))),
% 0.69/0.88      inference('demod', [status(thm)], ['43', '44'])).
% 0.69/0.88  thf('46', plain,
% 0.69/0.88      ((~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.69/0.88        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.69/0.88        | ~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['40', '45'])).
% 0.69/0.88  thf('47', plain,
% 0.69/0.88      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['13', '37'])).
% 0.69/0.88  thf('48', plain,
% 0.69/0.88      ((~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.69/0.88        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.88      inference('demod', [status(thm)], ['46', '47'])).
% 0.69/0.88  thf('49', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('50', plain,
% 0.69/0.88      (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('clc', [status(thm)], ['48', '49'])).
% 0.69/0.88  thf('51', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('52', plain,
% 0.69/0.88      ((m1_subset_1 @ 
% 0.69/0.88        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['33', '34'])).
% 0.69/0.88  thf(t42_subset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.88       ( ![C:$i]:
% 0.69/0.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.88           ( r1_tarski @
% 0.69/0.88             ( k3_subset_1 @ A @ B ) @ 
% 0.69/0.88             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.88  thf('53', plain,
% 0.69/0.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.69/0.88          | (r1_tarski @ (k3_subset_1 @ X20 @ X21) @ 
% 0.69/0.88             (k3_subset_1 @ X20 @ (k9_subset_1 @ X20 @ X21 @ X19)))
% 0.69/0.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t42_subset_1])).
% 0.69/0.88  thf('54', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.88          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.69/0.88             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.88              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.69/0.88               (k2_pre_topc @ sk_A @ 
% 0.69/0.88                (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['52', '53'])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.88         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.88          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['51', '54'])).
% 0.69/0.88  thf('56', plain,
% 0.69/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.69/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('57', plain,
% 0.69/0.88      (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.88         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.88            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.69/0.88      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 0.69/0.88  thf('58', plain,
% 0.69/0.88      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.88         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['38', '39'])).
% 0.69/0.88  thf('59', plain,
% 0.69/0.88      ((r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.69/0.88        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.69/0.88  thf('60', plain, ($false), inference('demod', [status(thm)], ['50', '59'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
