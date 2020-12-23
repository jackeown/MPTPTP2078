%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hjff3wrCzt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:28 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 150 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  619 (1669 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(t28_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( ( v2_tops_2 @ B @ A )
              & ( v1_finset_1 @ B ) )
           => ( v4_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( ( v2_tops_2 @ B @ A )
                & ( v1_finset_1 @ B ) )
             => ( v4_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k5_setfam_1 @ X5 @ X4 )
        = ( k3_tarski @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('5',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v4_pre_topc @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ ( k3_tarski @ sk_B ) )
    | ( v4_pre_topc @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( k3_tarski @ sk_B ) )
    | ( v4_pre_topc @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v4_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    ~ ( v4_pre_topc @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k3_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_tops_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ X12 @ ( k7_setfam_1 @ X12 @ X11 ) )
        = ( k3_subset_1 @ X12 @ ( k5_setfam_1 @ X12 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_tops_2])).

thf('18',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('23',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t27_tops_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( ( v1_tops_2 @ B @ A )
              & ( v1_finset_1 @ B ) )
           => ( v3_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ( v3_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ X18 )
      | ~ ( v1_finset_1 @ X17 )
      | ~ ( v1_tops_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_2])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v3_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v2_tops_2 @ X15 @ X16 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) )
          <=> ( v1_finset_1 @ B ) ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_finset_1 @ X13 )
      | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X14 ) @ X13 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_tops_2])).

thf('36',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v1_finset_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('38',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_finset_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,(
    v3_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['25','26','27','33','41'])).

thf('43',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X10 ) @ X9 ) @ X10 )
      | ( v4_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_tarski @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v4_pre_topc @ ( k3_tarski @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v4_pre_topc @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('50',plain,(
    ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['43','50'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('52',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['15','51','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hjff3wrCzt
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 63 iterations in 0.051s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.54  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.54  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.36/0.54  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.54  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.36/0.54  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.36/0.54  thf(t28_tops_2, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @
% 0.36/0.54             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54           ( ( ( v2_tops_2 @ B @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.36/0.54             ( v4_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( m1_subset_1 @
% 0.36/0.54                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54              ( ( ( v2_tops_2 @ B @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.36/0.54                ( v4_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t28_tops_2])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_k5_setfam_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.54       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((m1_subset_1 @ (k5_setfam_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k5_setfam_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.54       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i]:
% 0.36/0.54         (((k5_setfam_1 @ X5 @ X4) = (k3_tarski @ X4))
% 0.36/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '5'])).
% 0.36/0.54  thf(cc2_pre_topc, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.36/0.54          | (v4_pre_topc @ X6 @ X7)
% 0.36/0.54          | ~ (v1_xboole_0 @ X6)
% 0.36/0.54          | ~ (l1_pre_topc @ X7)
% 0.36/0.54          | ~ (v2_pre_topc @ X7))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | ~ (v1_xboole_0 @ (k3_tarski @ sk_B))
% 0.36/0.54        | (v4_pre_topc @ (k3_tarski @ sk_B) @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.54  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      ((~ (v1_xboole_0 @ (k3_tarski @ sk_B))
% 0.36/0.54        | (v4_pre_topc @ (k3_tarski @ sk_B) @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (~ (v4_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('14', plain, (~ (v4_pre_topc @ (k3_tarski @ sk_B) @ sk_A)),
% 0.36/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('15', plain, (~ (v1_xboole_0 @ (k3_tarski @ sk_B))),
% 0.36/0.54      inference('clc', [status(thm)], ['11', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t11_tops_2, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.54         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.36/0.54           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         (((X11) = (k1_xboole_0))
% 0.36/0.54          | ((k6_setfam_1 @ X12 @ (k7_setfam_1 @ X12 @ X11))
% 0.36/0.54              = (k3_subset_1 @ X12 @ (k5_setfam_1 @ X12 @ X11)))
% 0.36/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.36/0.54      inference('cnf', [status(esa)], [t11_tops_2])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.54          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.36/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      ((((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.54          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B)))
% 0.36/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_k7_setfam_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.54       ( m1_subset_1 @
% 0.36/0.54         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]:
% 0.36/0.54         ((m1_subset_1 @ (k7_setfam_1 @ X2 @ X3) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2)))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2))))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf(t27_tops_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @
% 0.36/0.54             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54           ( ( ( v1_tops_2 @ B @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.36/0.54             ( v3_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X17 : $i, X18 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X17 @ 
% 0.36/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.36/0.54          | (v3_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X18) @ X17) @ X18)
% 0.36/0.54          | ~ (v1_finset_1 @ X17)
% 0.36/0.54          | ~ (v1_tops_2 @ X17 @ X18)
% 0.36/0.54          | ~ (l1_pre_topc @ X18)
% 0.36/0.54          | ~ (v2_pre_topc @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [t27_tops_2])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.36/0.54        | ~ (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.54        | (v3_pre_topc @ 
% 0.36/0.54           (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.36/0.54           sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t16_tops_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @
% 0.36/0.54             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54           ( ( v2_tops_2 @ B @ A ) <=>
% 0.36/0.54             ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X15 : $i, X16 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X15 @ 
% 0.36/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.36/0.54          | ~ (v2_tops_2 @ X15 @ X16)
% 0.36/0.54          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X16) @ X15) @ X16)
% 0.36/0.54          | ~ (l1_pre_topc @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.36/0.54        | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.54  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('32', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.36/0.54      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t13_tops_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_struct_0 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @
% 0.36/0.54             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54           ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.36/0.54             ( v1_finset_1 @ B ) ) ) ) ))).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X13 @ 
% 0.36/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.36/0.54          | ~ (v1_finset_1 @ X13)
% 0.36/0.54          | (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ X14) @ X13))
% 0.36/0.54          | ~ (l1_struct_0 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t13_tops_2])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      ((~ (l1_struct_0 @ sk_A)
% 0.36/0.54        | (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.54        | ~ (v1_finset_1 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.54  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_l1_pre_topc, axiom,
% 0.36/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.54  thf('38', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.54  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf('40', plain, ((v1_finset_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      ((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['36', '39', '40'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      ((v3_pre_topc @ 
% 0.36/0.54        (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.36/0.54        sk_A)),
% 0.36/0.54      inference('demod', [status(thm)], ['25', '26', '27', '33', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (((v3_pre_topc @ 
% 0.36/0.54         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B)) @ sk_A)
% 0.36/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['20', '42'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '5'])).
% 0.36/0.54  thf(t29_tops_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.54             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      (![X9 : $i, X10 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.36/0.54          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X10) @ X9) @ X10)
% 0.36/0.54          | (v4_pre_topc @ X9 @ X10)
% 0.36/0.54          | ~ (l1_pre_topc @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | (v4_pre_topc @ (k3_tarski @ sk_B) @ sk_A)
% 0.36/0.54        | ~ (v3_pre_topc @ 
% 0.36/0.54             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B)) @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.54  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (((v4_pre_topc @ (k3_tarski @ sk_B) @ sk_A)
% 0.36/0.54        | ~ (v3_pre_topc @ 
% 0.36/0.54             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B)) @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.54  thf('49', plain, (~ (v4_pre_topc @ (k3_tarski @ sk_B) @ sk_A)),
% 0.36/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (~ (v3_pre_topc @ 
% 0.36/0.54          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B)) @ sk_A)),
% 0.36/0.54      inference('clc', [status(thm)], ['48', '49'])).
% 0.36/0.54  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('clc', [status(thm)], ['43', '50'])).
% 0.36/0.54  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.36/0.54  thf('52', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.36/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.54  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('54', plain, ($false),
% 0.36/0.54      inference('demod', [status(thm)], ['15', '51', '52', '53'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
