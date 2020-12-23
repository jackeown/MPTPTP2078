%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TcBukRFHHn

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 244 expanded)
%              Number of leaves         :   37 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          : 1031 (2412 expanded)
%              Number of equality atoms :   53 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('26',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( v3_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('36',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('41',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tops_1 @ X26 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('47',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v2_tops_1 @ X30 @ X31 )
      | ~ ( v3_tops_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['41','52','53','54'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('57',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['65','66'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('68',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('69',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('70',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_tops_1 @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc3_tops_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('82',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( v3_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_1 @ k1_xboole_0 @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_1 @ k1_xboole_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['75','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('98',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['38','96','101'])).

thf('103',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TcBukRFHHn
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 313 iterations in 0.106s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.20/0.56  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(t97_tops_1, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.20/0.56             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.20/0.56                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.20/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.56         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d5_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.20/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.56         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_k3_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]:
% 0.20/0.56         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.20/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf(d3_tops_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.56             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.56          | ~ (v1_tops_1 @ X20 @ X21)
% 0.20/0.56          | ((k2_pre_topc @ X21 @ X20) = (k2_struct_0 @ X21))
% 0.20/0.56          | ~ (l1_pre_topc @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.56            = (k2_struct_0 @ sk_A))
% 0.20/0.56        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.56          = (k2_struct_0 @ sk_A))
% 0.20/0.56        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf(t52_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.56             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.56               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.56          | ~ (v4_pre_topc @ X16 @ X17)
% 0.20/0.56          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.20/0.56          | ~ (l1_pre_topc @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.56            = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.56        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.56          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.56        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t30_tops_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.56             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X24 : $i, X25 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.56          | ~ (v3_pre_topc @ X24 @ X25)
% 0.20/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 0.20/0.56          | ~ (l1_pre_topc @ X25))),
% 0.20/0.56      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.56        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.56  thf('26', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['20', '27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))
% 0.20/0.56        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['15', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t91_tops_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v3_tops_1 @ B @ A ) =>
% 0.20/0.56             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X28 : $i, X29 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.56          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.20/0.56          | ~ (v3_tops_1 @ X28 @ X29)
% 0.20/0.56          | ~ (l1_pre_topc @ X29))),
% 0.20/0.56      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.20/0.56        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('34', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['29', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(fc9_tops_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X22)
% 0.20/0.56          | ~ (v2_pre_topc @ X22)
% 0.20/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.56          | (v3_pre_topc @ (k1_tops_1 @ X22 @ X23) @ X22))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t84_tops_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.56             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X26 : $i, X27 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.56          | ~ (v2_tops_1 @ X26 @ X27)
% 0.20/0.56          | ((k1_tops_1 @ X27 @ X26) = (k1_xboole_0))
% 0.20/0.56          | ~ (l1_pre_topc @ X27))),
% 0.20/0.56      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.56        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t92_tops_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X30 : $i, X31 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.20/0.56          | (v2_tops_1 @ X30 @ X31)
% 0.20/0.56          | ~ (v3_tops_1 @ X30 @ X31)
% 0.20/0.56          | ~ (l1_pre_topc @ X31))),
% 0.20/0.56      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.20/0.56        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.56  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('50', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('51', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.56  thf('52', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['44', '45', '51'])).
% 0.20/0.56  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('55', plain, ((v3_pre_topc @ k1_xboole_0 @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['41', '52', '53', '54'])).
% 0.20/0.56  thf(t4_subset_1, axiom,
% 0.20/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      (![X24 : $i, X25 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.56          | ~ (v3_pre_topc @ X24 @ X25)
% 0.20/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 0.20/0.56          | ~ (l1_pre_topc @ X25))),
% 0.20/0.56      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.20/0.56             X0)
% 0.20/0.56          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.20/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.56  thf(t3_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.56  thf('62', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.56  thf('63', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.56          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['58', '63'])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      (((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['55', '64'])).
% 0.20/0.56  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('67', plain, ((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.56  thf(dt_k2_subset_1, axiom,
% 0.20/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.56  thf('68', plain,
% 0.20/0.56      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.56  thf('69', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.56  thf('70', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.20/0.56      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.56          | ~ (v4_pre_topc @ X16 @ X17)
% 0.20/0.56          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.20/0.56          | ~ (l1_pre_topc @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.56  thf('72', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.20/0.56          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['67', '72'])).
% 0.20/0.56  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf(cc3_tops_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v1_xboole_0 @ B ) => ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      (![X18 : $i, X19 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.56          | (v3_tops_1 @ X18 @ X19)
% 0.20/0.56          | ~ (v1_xboole_0 @ X18)
% 0.20/0.56          | ~ (l1_pre_topc @ X19)
% 0.20/0.56          | ~ (v2_pre_topc @ X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc3_tops_1])).
% 0.20/0.56  thf('78', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.56          | (v3_tops_1 @ k1_xboole_0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.56  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.56  thf('80', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | (v3_tops_1 @ k1_xboole_0 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.56  thf('81', plain,
% 0.20/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf('82', plain,
% 0.20/0.56      (![X28 : $i, X29 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.56          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.20/0.56          | ~ (v3_tops_1 @ X28 @ X29)
% 0.20/0.56          | ~ (l1_pre_topc @ X29))),
% 0.20/0.56      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v3_tops_1 @ k1_xboole_0 @ X0)
% 0.20/0.56          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.56  thf('84', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v3_tops_1 @ k1_xboole_0 @ X0)
% 0.20/0.56          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['83', '84'])).
% 0.20/0.56  thf('86', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v2_pre_topc @ X0)
% 0.20/0.56          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['80', '85'])).
% 0.20/0.56  thf('87', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.56          | ~ (v2_pre_topc @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['86'])).
% 0.20/0.56  thf('88', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.20/0.56      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.56  thf('89', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.56          | ~ (v1_tops_1 @ X20 @ X21)
% 0.20/0.56          | ((k2_pre_topc @ X21 @ X20) = (k2_struct_0 @ X21))
% 0.20/0.56          | ~ (l1_pre_topc @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.20/0.56  thf('90', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.20/0.56          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v2_pre_topc @ X0)
% 0.20/0.56          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['87', '90'])).
% 0.20/0.56  thf('92', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.20/0.56          | ~ (v2_pre_topc @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.56  thf('93', plain,
% 0.20/0.56      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup+', [status(thm)], ['75', '92'])).
% 0.20/0.56  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('96', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.20/0.56  thf('97', plain,
% 0.20/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf('98', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.20/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.56  thf('99', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.56  thf('100', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.56  thf('101', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['99', '100'])).
% 0.20/0.56  thf('102', plain, (((k1_xboole_0) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['38', '96', '101'])).
% 0.20/0.56  thf('103', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('104', plain, ($false),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
