%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2046+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DOKKGLiYyT

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 142 expanded)
%              Number of leaves         :   37 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  693 (1344 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t5_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) )
        & ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_orders_2 @ ( g1_orders_2 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( v1_orders_2 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( g1_orders_2 @ X14 @ X15 )
       != ( g1_orders_2 @ X12 @ X13 ) )
      | ( X14 = X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_orders_2 @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) )
      | ( ( u1_struct_0 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( l1_orders_2 @ ( g1_orders_2 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( l1_struct_0 @ ( g1_orders_2 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['21','22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_yellow19 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k1_yellow19 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X4 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow19])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t4_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
             => ( ( r2_waybel_7 @ A @ C @ B )
              <=> ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_tarski @ ( k1_yellow19 @ X20 @ X19 ) @ X21 )
      | ( r2_waybel_7 @ X20 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow19])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ X0 ) @ ( k1_yellow19 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v1_xboole_0 @ ( k1_yellow19 @ A @ B ) )
        & ( v1_subset_1 @ ( k1_yellow19 @ A @ B ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
        & ( v2_waybel_0 @ ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
        & ( v13_waybel_0 @ ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( v13_waybel_0 @ ( k1_yellow19 @ X10 @ X11 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow19])).

thf('41',plain,
    ( ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ X0 ) @ ( k1_yellow19 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','46'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).


%------------------------------------------------------------------------------
