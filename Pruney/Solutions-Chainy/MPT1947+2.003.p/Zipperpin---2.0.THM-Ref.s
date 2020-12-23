%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.igPdbrICQB

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 489 expanded)
%              Number of leaves         :   37 ( 161 expanded)
%              Depth                    :   24
%              Number of atoms          : 1146 (7846 expanded)
%              Number of equality atoms :   18 ( 236 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t45_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( k11_yellow_6 @ A @ B )
            = ( k4_yellow_6 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v8_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A )
              & ( l1_waybel_0 @ B @ A ) )
           => ( ( k11_yellow_6 @ A @ B )
              = ( k4_yellow_6 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_yellow_6])).

thf('7',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t25_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( k2_waybel_0 @ A @ B @ C )
                = ( k4_yellow_6 @ A @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v7_waybel_0 @ X26 )
      | ~ ( v1_yellow_6 @ X26 @ X27 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ( ( k2_waybel_0 @ X27 @ X26 @ X28 )
        = ( k4_yellow_6 @ X27 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_6])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ X0 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) )
        = ( k4_yellow_6 @ X1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v1_yellow_6 @ X0 @ X1 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_yellow_6 @ sk_B_1 @ sk_A )
    | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','20'])).

thf('22',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X19 @ X18 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( v1_yellow_6 @ X29 @ X30 )
      | ~ ( l1_waybel_0 @ X29 @ X30 )
      | ( r2_hidden @ ( k4_yellow_6 @ X30 @ X29 ) @ ( k10_yellow_6 @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_6])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(d20_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v3_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( C
                  = ( k11_yellow_6 @ A @ B ) )
              <=> ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( v3_yellow_6 @ X23 @ X24 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( r2_hidden @ X25 @ ( k10_yellow_6 @ X24 @ X23 ) )
      | ( X25
        = ( k11_yellow_6 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d20_yellow_6])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_yellow_6 @ sk_A @ sk_B_1 )
      = ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v3_yellow_6 @ sk_B_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v3_yellow_6 @ B @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( v3_yellow_6 @ X21 @ X22 )
      | ~ ( v1_yellow_6 @ X21 @ X22 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_6])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_yellow_6 @ sk_B_1 @ sk_A )
    | ( v3_yellow_6 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v3_yellow_6 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v3_yellow_6 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_yellow_6 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_yellow_6 @ sk_A @ sk_B_1 )
      = ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46','47','48','49','62','63','64'])).

thf('66',plain,(
    ( k11_yellow_6 @ sk_A @ sk_B_1 )
 != ( k4_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( m1_subset_1 @ X5 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('78',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X19 @ X18 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X2 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X0 @ sk_B_1 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('86',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( m1_subset_1 @ X5 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('87',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v7_waybel_0 @ X26 )
      | ~ ( v1_yellow_6 @ X26 @ X27 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ( ( k2_waybel_0 @ X27 @ X26 @ X28 )
        = ( k4_yellow_6 @ X27 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_6])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 )
      | ( ( k2_waybel_0 @ X2 @ X0 @ X1 )
        = ( k4_yellow_6 @ X2 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X2 )
      | ~ ( v1_yellow_6 @ X0 @ X2 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v1_yellow_6 @ sk_B_1 @ X0 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
      | ( ( k2_waybel_0 @ X0 @ sk_B_1 @ X1 )
        = ( k4_yellow_6 @ X0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_yellow_6 @ sk_B_1 @ X0 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
      | ( ( k2_waybel_0 @ X0 @ sk_B_1 @ X1 )
        = ( k4_yellow_6 @ X0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('95',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.igPdbrICQB
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 100 iterations in 0.077s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.21/0.54  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.21/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.54  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.54  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.21/0.54  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(t4_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('2', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf(d1_xboole_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf(t7_ordinal1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.54  thf(t45_yellow_6, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54           ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54                ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.54                ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54              ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t45_yellow_6])).
% 0.21/0.54  thf('7', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf(t1_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf(t25_yellow_6, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.54               ( ( k2_waybel_0 @ A @ B @ C ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X26)
% 0.21/0.54          | ~ (v4_orders_2 @ X26)
% 0.21/0.54          | ~ (v7_waybel_0 @ X26)
% 0.21/0.54          | ~ (v1_yellow_6 @ X26 @ X27)
% 0.21/0.54          | ~ (l1_waybel_0 @ X26 @ X27)
% 0.21/0.54          | ((k2_waybel_0 @ X27 @ X26 @ X28) = (k4_yellow_6 @ X27 @ X26))
% 0.21/0.54          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.21/0.54          | ~ (l1_struct_0 @ X27)
% 0.21/0.54          | (v2_struct_0 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [t25_yellow_6])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.54          | (v2_struct_0 @ X1)
% 0.21/0.54          | ~ (l1_struct_0 @ X1)
% 0.21/0.54          | ((k2_waybel_0 @ X1 @ X0 @ (sk_B @ (u1_struct_0 @ X0)))
% 0.21/0.54              = (k4_yellow_6 @ X1 @ X0))
% 0.21/0.54          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.54          | ~ (v1_yellow_6 @ X0 @ X1)
% 0.21/0.54          | ~ (v7_waybel_0 @ X0)
% 0.21/0.54          | ~ (v4_orders_2 @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v1_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.54        | ((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.54            = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.54  thf('15', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_l1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | ((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.54            = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['14', '15', '16', '17', '20'])).
% 0.21/0.54  thf('22', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf(dt_k2_waybel_0, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.54         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.54          | (v2_struct_0 @ X18)
% 0.21/0.54          | ~ (l1_struct_0 @ X19)
% 0.21/0.54          | (v2_struct_0 @ X19)
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.21/0.54          | (m1_subset_1 @ (k2_waybel_0 @ X19 @ X18 @ X20) @ 
% 0.21/0.54             (u1_struct_0 @ X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.54          | (m1_subset_1 @ 
% 0.21/0.54             (k2_waybel_0 @ X1 @ X0 @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.21/0.54             (u1_struct_0 @ X1))
% 0.21/0.54          | (v2_struct_0 @ X1)
% 0.21/0.54          | ~ (l1_struct_0 @ X1)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (l1_waybel_0 @ X0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (m1_subset_1 @ 
% 0.21/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.54  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (m1_subset_1 @ 
% 0.21/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['21', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54        | (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf('31', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t42_yellow_6, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X29)
% 0.21/0.54          | ~ (v4_orders_2 @ X29)
% 0.21/0.54          | ~ (v7_waybel_0 @ X29)
% 0.21/0.54          | ~ (v1_yellow_6 @ X29 @ X30)
% 0.21/0.54          | ~ (l1_waybel_0 @ X29 @ X30)
% 0.21/0.54          | (r2_hidden @ (k4_yellow_6 @ X30 @ X29) @ (k10_yellow_6 @ X30 @ X29))
% 0.21/0.54          | ~ (l1_pre_topc @ X30)
% 0.21/0.54          | ~ (v2_pre_topc @ X30)
% 0.21/0.54          | (v2_struct_0 @ X30))),
% 0.21/0.54      inference('cnf', [status(esa)], [t42_yellow_6])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('37', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('38', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.21/0.54  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf('42', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf(d20_yellow_6, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54               ( ( ( C ) = ( k11_yellow_6 @ A @ B ) ) <=>
% 0.21/0.54                 ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X23)
% 0.21/0.54          | ~ (v4_orders_2 @ X23)
% 0.21/0.54          | ~ (v7_waybel_0 @ X23)
% 0.21/0.54          | ~ (v3_yellow_6 @ X23 @ X24)
% 0.21/0.54          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.21/0.54          | ~ (r2_hidden @ X25 @ (k10_yellow_6 @ X24 @ X23))
% 0.21/0.54          | ((X25) = (k11_yellow_6 @ X24 @ X23))
% 0.21/0.54          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.21/0.54          | ~ (l1_pre_topc @ X24)
% 0.21/0.54          | ~ (v8_pre_topc @ X24)
% 0.21/0.54          | ~ (v2_pre_topc @ X24)
% 0.21/0.54          | (v2_struct_0 @ X24))),
% 0.21/0.54      inference('cnf', [status(esa)], [d20_yellow_6])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((k4_yellow_6 @ sk_A @ sk_B_1) = (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.54        | ~ (v3_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('47', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc4_yellow_6, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.54           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54               ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) ) =>
% 0.21/0.54             ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54               ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (l1_waybel_0 @ X21 @ X22)
% 0.21/0.54          | (v3_yellow_6 @ X21 @ X22)
% 0.21/0.54          | ~ (v1_yellow_6 @ X21 @ X22)
% 0.21/0.54          | ~ (v7_waybel_0 @ X21)
% 0.21/0.54          | ~ (v4_orders_2 @ X21)
% 0.21/0.54          | (v2_struct_0 @ X21)
% 0.21/0.54          | ~ (l1_pre_topc @ X22)
% 0.21/0.54          | ~ (v2_pre_topc @ X22)
% 0.21/0.54          | (v2_struct_0 @ X22))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc4_yellow_6])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v1_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.54        | (v3_yellow_6 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('55', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('57', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v3_yellow_6 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '53', '54', '55', '56', '57'])).
% 0.21/0.54  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain, (((v3_yellow_6 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('62', plain, ((v3_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf('63', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('64', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((k4_yellow_6 @ sk_A @ sk_B_1) = (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['45', '46', '47', '48', '49', '62', '63', '64'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (((k11_yellow_6 @ sk_A @ sk_B_1) != (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.21/0.54  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf('70', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      (~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '71'])).
% 0.21/0.54  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['72', '73'])).
% 0.21/0.54  thf('75', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('76', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.54  thf(d2_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X5) | (m1_subset_1 @ X5 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.54          | (v2_struct_0 @ X18)
% 0.21/0.54          | ~ (l1_struct_0 @ X19)
% 0.21/0.54          | (v2_struct_0 @ X19)
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.21/0.54          | (m1_subset_1 @ (k2_waybel_0 @ X19 @ X18 @ X20) @ 
% 0.21/0.54             (u1_struct_0 @ X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (v1_xboole_0 @ X1)
% 0.21/0.54          | (m1_subset_1 @ (k2_waybel_0 @ X2 @ X0 @ X1) @ (u1_struct_0 @ X2))
% 0.21/0.54          | (v2_struct_0 @ X2)
% 0.21/0.54          | ~ (l1_struct_0 @ X2)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (l1_waybel_0 @ X0 @ X2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (l1_waybel_0 @ sk_B_1 @ X0)
% 0.21/0.54          | (v2_struct_0 @ sk_B_1)
% 0.21/0.54          | ~ (l1_struct_0 @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | (m1_subset_1 @ (k2_waybel_0 @ X0 @ sk_B_1 @ X1) @ 
% 0.21/0.54             (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['76', '79'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X0)
% 0.21/0.54          | (m1_subset_1 @ (k2_waybel_0 @ sk_A @ sk_B_1 @ X0) @ 
% 0.21/0.54             (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '80'])).
% 0.21/0.54  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X0)
% 0.21/0.54          | (m1_subset_1 @ (k2_waybel_0 @ sk_A @ sk_B_1 @ X0) @ 
% 0.21/0.54             (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.54  thf('84', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('85', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X5) | (m1_subset_1 @ X5 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X26)
% 0.21/0.54          | ~ (v4_orders_2 @ X26)
% 0.21/0.54          | ~ (v7_waybel_0 @ X26)
% 0.21/0.54          | ~ (v1_yellow_6 @ X26 @ X27)
% 0.21/0.54          | ~ (l1_waybel_0 @ X26 @ X27)
% 0.21/0.54          | ((k2_waybel_0 @ X27 @ X26 @ X28) = (k4_yellow_6 @ X27 @ X26))
% 0.21/0.54          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.21/0.54          | ~ (l1_struct_0 @ X27)
% 0.21/0.54          | (v2_struct_0 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [t25_yellow_6])).
% 0.21/0.54  thf('88', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (v1_xboole_0 @ X1)
% 0.21/0.54          | (v2_struct_0 @ X2)
% 0.21/0.54          | ~ (l1_struct_0 @ X2)
% 0.21/0.54          | ((k2_waybel_0 @ X2 @ X0 @ X1) = (k4_yellow_6 @ X2 @ X0))
% 0.21/0.54          | ~ (l1_waybel_0 @ X0 @ X2)
% 0.21/0.54          | ~ (v1_yellow_6 @ X0 @ X2)
% 0.21/0.54          | ~ (v7_waybel_0 @ X0)
% 0.21/0.54          | ~ (v4_orders_2 @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B_1)
% 0.21/0.54          | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54          | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54          | ~ (v1_yellow_6 @ sk_B_1 @ X0)
% 0.21/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ X0)
% 0.21/0.54          | ((k2_waybel_0 @ X0 @ sk_B_1 @ X1) = (k4_yellow_6 @ X0 @ sk_B_1))
% 0.21/0.54          | ~ (l1_struct_0 @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['85', '88'])).
% 0.21/0.54  thf('90', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('91', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B_1)
% 0.21/0.54          | ~ (v1_yellow_6 @ sk_B_1 @ X0)
% 0.21/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ X0)
% 0.21/0.54          | ((k2_waybel_0 @ X0 @ sk_B_1 @ X1) = (k4_yellow_6 @ X0 @ sk_B_1))
% 0.21/0.54          | ~ (l1_struct_0 @ X0)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X0)
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.54          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ X0) = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['84', '92'])).
% 0.21/0.54  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('95', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X0)
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ X0) = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.21/0.54  thf('97', plain,
% 0.21/0.54      (~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('98', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ (k2_waybel_0 @ sk_A @ sk_B_1 @ X0) @ 
% 0.21/0.54             (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_B_1)
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B_1)
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_xboole_0 @ X0)
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['83', '98'])).
% 0.21/0.54  thf('100', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X0) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('simplify', [status(thm)], ['99'])).
% 0.21/0.54  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('102', plain,
% 0.21/0.54      (![X0 : $i]: ((v2_struct_0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.54  thf('103', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('104', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.21/0.54      inference('clc', [status(thm)], ['102', '103'])).
% 0.21/0.54  thf('105', plain, ($false), inference('sup-', [status(thm)], ['6', '104'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
