%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xM2JCqNpla

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:13 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 458 expanded)
%              Number of leaves         :   42 ( 146 expanded)
%              Depth                    :   19
%              Number of atoms          :  975 (5393 expanded)
%              Number of equality atoms :   24 (  50 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v1_tops_1 @ X32 @ X33 )
      | ~ ( v3_tex_2 @ X32 @ X33 )
      | ~ ( v3_pre_topc @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_tdlat_3 @ X28 )
      | ( v3_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('12',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( r1_tarski @ ( k2_pre_topc @ X21 @ X22 ) @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_tdlat_3 @ X28 )
      | ( v3_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['34','35','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_B_1 )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('57',plain,(
    ! [X11: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('58',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('59',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('60',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('63',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','61','62'])).

thf('64',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('66',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('67',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('68',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ X12 @ X12 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','69','70'])).

thf('72',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('74',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v3_tex_2 @ X34 @ X35 )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ~ ( v1_tops_1 @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v2_tex_2 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_tdlat_3 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','86'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('88',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('90',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('91',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('93',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( sk_B_1
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('96',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf(fc12_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('99',plain,(
    ! [X17: $i] :
      ( ( v1_tops_1 @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc12_tops_1])).

thf('100',plain,
    ( ( ( v1_tops_1 @ sk_B_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','69'])).

thf('104',plain,(
    v1_tops_1 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['72','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xM2JCqNpla
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:46:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 291 iterations in 0.177s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.63  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.45/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.45/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.63  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.63  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.63  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(t49_tex_2, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.45/0.63         ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v3_tex_2 @ B @ A ) <=>
% 0.45/0.63             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.63            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63          ( ![B:$i]:
% 0.45/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63              ( ( v3_tex_2 @ B @ A ) <=>
% 0.45/0.63                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.63        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.63        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.45/0.63       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t47_tex_2, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.45/0.63             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X32 : $i, X33 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.45/0.63          | (v1_tops_1 @ X32 @ X33)
% 0.45/0.63          | ~ (v3_tex_2 @ X32 @ X33)
% 0.45/0.63          | ~ (v3_pre_topc @ X32 @ X33)
% 0.45/0.63          | ~ (l1_pre_topc @ X33)
% 0.45/0.63          | ~ (v2_pre_topc @ X33)
% 0.45/0.63          | (v2_struct_0 @ X33))),
% 0.45/0.63      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.45/0.63        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.45/0.63        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t17_tdlat_3, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ( v1_tdlat_3 @ A ) <=>
% 0.45/0.63         ( ![B:$i]:
% 0.45/0.63           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X28 : $i, X29 : $i]:
% 0.45/0.63         (~ (v1_tdlat_3 @ X28)
% 0.45/0.63          | (v3_pre_topc @ X29 @ X28)
% 0.45/0.63          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.63          | ~ (l1_pre_topc @ X28)
% 0.45/0.63          | ~ (v2_pre_topc @ X28))),
% 0.45/0.63      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.45/0.63        | ~ (v1_tdlat_3 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('15', plain, ((v1_tdlat_3 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('16', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.45/0.63        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['7', '8', '9', '16'])).
% 0.45/0.63  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('clc', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d2_tops_3, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v1_tops_1 @ B @ A ) <=>
% 0.45/0.63             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X24 : $i, X25 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.45/0.63          | ~ (v1_tops_1 @ X24 @ X25)
% 0.45/0.63          | ((k2_pre_topc @ X25 @ X24) = (u1_struct_0 @ X25))
% 0.45/0.63          | ~ (l1_pre_topc @ X25))),
% 0.45/0.63      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.45/0.63        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.63  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.45/0.63        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.45/0.63         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '25'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t31_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.45/0.63                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.63          | ~ (v4_pre_topc @ X20 @ X21)
% 0.45/0.63          | ~ (r1_tarski @ X22 @ X20)
% 0.45/0.63          | (r1_tarski @ (k2_pre_topc @ X21 @ X22) @ X20)
% 0.45/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.63          | ~ (l1_pre_topc @ X21))),
% 0.45/0.63      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (l1_pre_topc @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B_1)
% 0.45/0.63          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.45/0.63          | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.63  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t29_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.63             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X18 : $i, X19 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.63          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18) @ X19)
% 0.45/0.63          | (v4_pre_topc @ X18 @ X19)
% 0.45/0.63          | ~ (l1_pre_topc @ X19))),
% 0.45/0.63      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.45/0.63        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k3_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i]:
% 0.45/0.63         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.45/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.45/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      (![X28 : $i, X29 : $i]:
% 0.45/0.63         (~ (v1_tdlat_3 @ X28)
% 0.45/0.63          | (v3_pre_topc @ X29 @ X28)
% 0.45/0.63          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.63          | ~ (l1_pre_topc @ X28)
% 0.45/0.63          | ~ (v2_pre_topc @ X28))),
% 0.45/0.63      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.45/0.63        | ~ (v1_tdlat_3 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.63  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('43', plain, ((v1_tdlat_3 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.45/0.63  thf('45', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['34', '35', '44'])).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B_1)
% 0.45/0.63          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['30', '31', '45'])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      ((~ (r1_tarski @ sk_B_1 @ sk_B_1)
% 0.45/0.63        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['27', '46'])).
% 0.45/0.63  thf(d10_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.63  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.63      inference('simplify', [status(thm)], ['48'])).
% 0.45/0.63  thf('50', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['47', '49'])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (![X0 : $i, X2 : $i]:
% 0.45/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      ((~ (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))
% 0.45/0.63        | ((sk_B_1) = (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (((~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.63         | ((sk_B_1) = (k2_pre_topc @ sk_A @ sk_B_1))))
% 0.45/0.63         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['26', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t2_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.63  thf('55', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i]:
% 0.45/0.63         ((r2_hidden @ X13 @ X14)
% 0.45/0.63          | (v1_xboole_0 @ X14)
% 0.45/0.63          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.63  thf(fc1_subset_1, axiom,
% 0.45/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.63  thf('57', plain, (![X11 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.63  thf(d1_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X6 @ X5)
% 0.45/0.63          | (r1_tarski @ X6 @ X4)
% 0.45/0.63          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (![X4 : $i, X6 : $i]:
% 0.45/0.63         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['59'])).
% 0.45/0.63  thf('61', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['58', '60'])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.45/0.63         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '25'])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['53', '61', '62'])).
% 0.45/0.63  thf('64', plain,
% 0.45/0.63      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.45/0.63         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.45/0.63             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['63', '64'])).
% 0.45/0.63  thf(fc14_subset_1, axiom,
% 0.45/0.63    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.45/0.63  thf('66', plain, (![X12 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X12) @ X12)),
% 0.45/0.63      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.45/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.63  thf('67', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.63  thf('68', plain, (![X12 : $i]: ~ (v1_subset_1 @ X12 @ X12)),
% 0.45/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.45/0.63       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['65', '68'])).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.45/0.63       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('71', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['3', '69', '70'])).
% 0.45/0.63  thf('72', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['1', '71'])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t48_tex_2, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.45/0.63             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      (![X34 : $i, X35 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.45/0.63          | (v3_tex_2 @ X34 @ X35)
% 0.45/0.63          | ~ (v2_tex_2 @ X34 @ X35)
% 0.45/0.63          | ~ (v1_tops_1 @ X34 @ X35)
% 0.45/0.63          | ~ (l1_pre_topc @ X35)
% 0.45/0.63          | ~ (v2_pre_topc @ X35)
% 0.45/0.63          | (v2_struct_0 @ X35))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.45/0.63        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.45/0.63        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.63  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('78', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t43_tex_2, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.45/0.63         ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.45/0.63  thf('79', plain,
% 0.45/0.63      (![X30 : $i, X31 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.45/0.63          | (v2_tex_2 @ X30 @ X31)
% 0.45/0.63          | ~ (l1_pre_topc @ X31)
% 0.45/0.63          | ~ (v1_tdlat_3 @ X31)
% 0.45/0.63          | ~ (v2_pre_topc @ X31)
% 0.45/0.63          | (v2_struct_0 @ X31))),
% 0.45/0.63      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.45/0.63  thf('80', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.63        | ~ (v1_tdlat_3 @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.63  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('82', plain, ((v1_tdlat_3 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('84', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.45/0.63  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('86', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.45/0.63      inference('clc', [status(thm)], ['84', '85'])).
% 0.45/0.63  thf('87', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.45/0.63        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['75', '76', '77', '86'])).
% 0.45/0.63  thf(d3_struct_0, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.63  thf('88', plain,
% 0.45/0.63      (![X15 : $i]:
% 0.45/0.63         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.63  thf('89', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d7_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.45/0.63  thf('90', plain,
% 0.45/0.63      (![X26 : $i, X27 : $i]:
% 0.45/0.63         (((X27) = (X26))
% 0.45/0.63          | (v1_subset_1 @ X27 @ X26)
% 0.45/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.45/0.63  thf('91', plain,
% 0.45/0.63      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.63        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['89', '90'])).
% 0.45/0.63  thf('92', plain,
% 0.45/0.63      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('93', plain,
% 0.45/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.45/0.63         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['91', '92'])).
% 0.45/0.63  thf('94', plain,
% 0.45/0.63      (((((sk_B_1) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.63         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['88', '93'])).
% 0.45/0.63  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_l1_pre_topc, axiom,
% 0.45/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.63  thf('96', plain,
% 0.45/0.63      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.63  thf('97', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['95', '96'])).
% 0.45/0.63  thf('98', plain,
% 0.45/0.63      ((((sk_B_1) = (k2_struct_0 @ sk_A)))
% 0.45/0.63         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('demod', [status(thm)], ['94', '97'])).
% 0.45/0.63  thf(fc12_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) => ( v1_tops_1 @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.63  thf('99', plain,
% 0.45/0.63      (![X17 : $i]:
% 0.45/0.63         ((v1_tops_1 @ (k2_struct_0 @ X17) @ X17) | ~ (l1_pre_topc @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc12_tops_1])).
% 0.45/0.63  thf('100', plain,
% 0.45/0.63      ((((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.45/0.63         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['98', '99'])).
% 0.45/0.63  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('102', plain,
% 0.45/0.63      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.45/0.63         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('demod', [status(thm)], ['100', '101'])).
% 0.45/0.63  thf('103', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['3', '69'])).
% 0.45/0.63  thf('104', plain, ((v1_tops_1 @ sk_B_1 @ sk_A)),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['102', '103'])).
% 0.45/0.63  thf('105', plain, (((v2_struct_0 @ sk_A) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['87', '104'])).
% 0.45/0.63  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('107', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.45/0.63      inference('clc', [status(thm)], ['105', '106'])).
% 0.45/0.63  thf('108', plain, ($false), inference('demod', [status(thm)], ['72', '107'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
