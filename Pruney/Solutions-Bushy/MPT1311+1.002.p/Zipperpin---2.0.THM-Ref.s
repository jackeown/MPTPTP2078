%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1311+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WzsQdPNvam

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:27 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 147 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  617 (1474 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t29_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
           => ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tops_2 @ B @ A )
             => ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k6_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('5',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v4_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_A_1 )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_xboole_0 @ ( k1_setfam_1 @ sk_B ) )
    | ( v4_pre_topc @ ( k1_setfam_1 @ sk_B ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( k1_setfam_1 @ sk_B ) )
    | ( v4_pre_topc @ ( k1_setfam_1 @ sk_B ) @ sk_A_1 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    ~ ( v4_pre_topc @ ( k1_setfam_1 @ sk_B ) @ sk_A_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k1_setfam_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_tops_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( ( k5_setfam_1 @ X17 @ ( k7_setfam_1 @ X17 @ X16 ) )
        = ( k3_subset_1 @ X17 @ ( k6_setfam_1 @ X17 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t12_tops_2])).

thf('18',plain,
    ( ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,
    ( ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k1_setfam_1 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('23',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t26_tops_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
           => ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( v1_tops_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t26_tops_2])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_A_1 )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) @ sk_A_1 )
    | ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v2_tops_2 @ X18 @ X19 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A_1 )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) @ sk_A_1 )
    | ~ ( v2_tops_2 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_tops_2 @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) @ sk_A_1 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A_1 ) @ sk_B ) ) @ sk_A_1 ),
    inference(demod,[status(thm)],['25','26','27','33'])).

thf('35',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k1_setfam_1 @ sk_B ) ) @ sk_A_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ( v4_pre_topc @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A_1 )
    | ( v4_pre_topc @ ( k1_setfam_1 @ sk_B ) @ sk_A_1 )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k1_setfam_1 @ sk_B ) ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v4_pre_topc @ ( k1_setfam_1 @ sk_B ) @ sk_A_1 )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k1_setfam_1 @ sk_B ) ) @ sk_A_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v4_pre_topc @ ( k1_setfam_1 @ sk_B ) @ sk_A_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('42',plain,(
    ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( k1_setfam_1 @ sk_B ) ) @ sk_A_1 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['35','42'])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X8: $i] :
      ( ( X8
       != ( k1_setfam_1 @ X3 ) )
      | ( X8 = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('45',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf(existence_l1_struct_0,axiom,(
    ? [A: $i] :
      ( l1_struct_0 @ A ) )).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[existence_l1_struct_0])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X13: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('48',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['15','43','45','53'])).


%------------------------------------------------------------------------------
