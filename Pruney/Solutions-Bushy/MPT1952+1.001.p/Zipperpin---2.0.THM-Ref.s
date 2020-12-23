%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1952+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tImP3OaIoQ

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:36 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  278 (11789 expanded)
%              Number of leaves         :   33 (3081 expanded)
%              Depth                    :   45
%              Number of atoms          : 3759 (301340 expanded)
%              Number of equality atoms :   35 (1929 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k13_yellow_6_type,type,(
    k13_yellow_6: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m4_yellow_6_type,type,(
    m4_yellow_6: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(a_2_1_yellow_6_type,type,(
    a_2_1_yellow_6: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v8_yellow_6_type,type,(
    v8_yellow_6: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t50_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( v8_yellow_6 @ B @ A )
            & ( m4_yellow_6 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k13_yellow_6 @ A @ B ) ) ) )
             => ( ( v3_pre_topc @ C @ ( k13_yellow_6 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                     => ! [E: $i] :
                          ( ( ~ ( v2_struct_0 @ E )
                            & ( v4_orders_2 @ E )
                            & ( v7_waybel_0 @ E )
                            & ( l1_waybel_0 @ E @ A ) )
                         => ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ B )
                           => ( r1_waybel_0 @ A @ E @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ( v8_yellow_6 @ B @ A )
              & ( m4_yellow_6 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k13_yellow_6 @ A @ B ) ) ) )
               => ( ( v3_pre_topc @ C @ ( k13_yellow_6 @ A @ B ) )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ C )
                       => ! [E: $i] :
                            ( ( ~ ( v2_struct_0 @ E )
                              & ( v4_orders_2 @ E )
                              & ( v7_waybel_0 @ E )
                              & ( l1_waybel_0 @ E @ A ) )
                           => ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ B )
                             => ( r1_waybel_0 @ A @ E @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_yellow_6])).

thf('0',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
   <= ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v2_struct_0 @ sk_E_1 )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v2_struct_0 @ sk_E_1 )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v4_orders_2 @ sk_E_1 )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v4_orders_2 @ sk_E_1 )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v7_waybel_0 @ sk_E_1 )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v7_waybel_0 @ sk_E_1 )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( l1_waybel_0 @ sk_E_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( l1_waybel_0 @ sk_E_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( v7_waybel_0 @ sk_E_1 )
   <= ( v7_waybel_0 @ sk_E_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('15',plain,
    ( ( v4_orders_2 @ sk_E_1 )
   <= ( v4_orders_2 @ sk_E_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( ( l1_waybel_0 @ sk_E_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_E_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('18',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k13_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ( m4_yellow_6 @ B @ A ) )
     => ( ( v1_pre_topc @ ( k13_yellow_6 @ A @ B ) )
        & ( l1_pre_topc @ ( k13_yellow_6 @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m4_yellow_6 @ X6 @ X5 )
      | ( v1_pre_topc @ ( k13_yellow_6 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k13_yellow_6])).

thf('20',plain,
    ( ( v1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(d27_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m4_yellow_6 @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k13_yellow_6 @ A @ B ) )
              <=> ( ( ( u1_struct_0 @ C )
                    = ( u1_struct_0 @ A ) )
                  & ( ( u1_pre_topc @ C )
                    = ( a_2_1_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m4_yellow_6 @ X0 @ X1 )
      | ( X2
       != ( k13_yellow_6 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ X2 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d27_yellow_6])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_pre_topc @ ( k13_yellow_6 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k13_yellow_6 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ ( k13_yellow_6 @ X1 @ X0 ) )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( m4_yellow_6 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( m4_yellow_6 @ sk_B @ sk_A )
    | ( ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m4_yellow_6 @ X6 @ X5 )
      | ( l1_pre_topc @ ( k13_yellow_6 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k13_yellow_6])).

thf('35',plain,
    ( ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
      | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
      | ~ ( l1_waybel_0 @ X17 @ sk_A )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( r2_hidden @ X16 @ sk_C )
      | ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ sk_C )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ X0 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_D_1 ) @ sk_B ) )
   <= ( ( r2_hidden @ sk_D_1 @ sk_C )
      & ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ X0 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_D_1 ) @ sk_B ) )
   <= ( ( r2_hidden @ sk_D_1 @ sk_C )
      & ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_E_1 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_E_1 )
      | ~ ( v4_orders_2 @ sk_E_1 )
      | ( v2_struct_0 @ sk_E_1 ) )
   <= ( ( r2_hidden @ sk_D_1 @ sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
      & ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','51'])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_E_1 )
      | ~ ( v4_orders_2 @ sk_E_1 )
      | ~ ( v7_waybel_0 @ sk_E_1 )
      | ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ) )
   <= ( ( r2_hidden @ sk_D_1 @ sk_C )
      & ( l1_waybel_0 @ sk_E_1 @ sk_A )
      & ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
      & ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','52'])).

thf('54',plain,
    ( ( ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_E_1 )
      | ( v2_struct_0 @ sk_E_1 ) )
   <= ( ( r2_hidden @ sk_D_1 @ sk_C )
      & ( v4_orders_2 @ sk_E_1 )
      & ( l1_waybel_0 @ sk_E_1 @ sk_A )
      & ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
      & ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','53'])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_E_1 )
      | ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ) )
   <= ( ( r2_hidden @ sk_D_1 @ sk_C )
      & ( v4_orders_2 @ sk_E_1 )
      & ( v7_waybel_0 @ sk_E_1 )
      & ( l1_waybel_0 @ sk_E_1 @ sk_A )
      & ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
      & ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','54'])).

thf('56',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
   <= ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_E_1 )
   <= ( ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
      & ( r2_hidden @ sk_D_1 @ sk_C )
      & ( v4_orders_2 @ sk_E_1 )
      & ( v7_waybel_0 @ sk_E_1 )
      & ( l1_waybel_0 @ sk_E_1 @ sk_A )
      & ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
      & ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v2_struct_0 @ sk_E_1 )
   <= ~ ( v2_struct_0 @ sk_E_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('59',plain,
    ( ~ ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) )
    | ( v2_struct_0 @ sk_E_1 )
    | ~ ( v7_waybel_0 @ sk_E_1 )
    | ~ ( l1_waybel_0 @ sk_E_1 @ sk_A )
    | ~ ( v4_orders_2 @ sk_E_1 )
    | ~ ( r2_hidden @ sk_D_1 @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(fraenkel_a_2_1_yellow_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_struct_0 @ B )
        & ( m4_yellow_6 @ C @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_yellow_6 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ D )
                 => ! [F: $i] :
                      ( ( ~ ( v2_struct_0 @ F )
                        & ( v4_orders_2 @ F )
                        & ( v7_waybel_0 @ F )
                        & ( l1_waybel_0 @ F @ B ) )
                     => ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ C )
                       => ( r1_waybel_0 @ B @ F @ D ) ) ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X9 != X10 )
      | ( v7_waybel_0 @ ( sk_F @ X10 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( v7_waybel_0 @ ( sk_F @ X10 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r2_hidden @ X10 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( v7_waybel_0 @ ( sk_F @ sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( v7_waybel_0 @ ( sk_F @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v7_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( v7_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ( v3_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C @ ( u1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('76',plain,
    ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C @ ( u1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m4_yellow_6 @ X0 @ X1 )
      | ( X2
       != ( k13_yellow_6 @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ X2 )
        = ( a_2_1_yellow_6 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d27_yellow_6])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_pre_topc @ ( k13_yellow_6 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k13_yellow_6 @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ ( k13_yellow_6 @ X1 @ X0 ) )
        = ( a_2_1_yellow_6 @ X1 @ X0 ) )
      | ~ ( m4_yellow_6 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( m4_yellow_6 @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      = ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( u1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      = ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( ( u1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      = ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('87',plain,
    ( ( u1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    = ( a_2_1_yellow_6 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','87'])).

thf('89',plain,
    ( ( v7_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
    | ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','88'])).

thf('90',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('92',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X9 != X10 )
      | ( v4_orders_2 @ ( sk_F @ X10 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('93',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( v4_orders_2 @ ( sk_F @ X10 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r2_hidden @ X10 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( v4_orders_2 @ ( sk_F @ sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( v4_orders_2 @ ( sk_F @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v4_orders_2 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( v4_orders_2 @ ( sk_F @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','87'])).

thf('101',plain,
    ( ( v4_orders_2 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
    | ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('104',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X9 != X10 )
      | ( l1_waybel_0 @ ( sk_F @ X10 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('105',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( l1_waybel_0 @ ( sk_F @ X10 @ X8 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r2_hidden @ X10 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( l1_waybel_0 @ ( sk_F @ sk_C @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( l1_waybel_0 @ ( sk_F @ sk_C @ X0 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( l1_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( l1_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('114',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X9 != X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X10 @ X8 @ X7 ) @ ( sk_E @ X10 @ X8 @ X7 ) ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('115',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F @ X10 @ X8 @ X7 ) @ ( sk_E @ X10 @ X8 @ X7 ) ) @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r2_hidden @ X10 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C @ X0 @ sk_A ) @ ( sk_E @ sk_C @ X0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C @ X0 @ sk_A ) @ ( sk_E @ sk_C @ X0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('124',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X9 != X10 )
      | ( r2_hidden @ ( sk_E @ X10 @ X8 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('125',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_E @ X10 @ X8 @ X7 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r2_hidden @ X10 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_C @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_C @ X0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('134',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X9 != X10 )
      | ( m1_subset_1 @ ( sk_E @ X10 @ X8 @ X7 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('135',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X10 @ X8 @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r2_hidden @ X10 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','135'])).

thf('137',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(split,[status(esa)],['47'])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ X0 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X0 @ sk_C )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ X0 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
        | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( l1_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','145'])).

thf('147',plain,
    ( ( ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','147'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','149'])).

thf('151',plain,
    ( ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','150'])).

thf('152',plain,
    ( ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('154',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X9 != X10 )
      | ~ ( r1_waybel_0 @ X7 @ ( sk_F @ X10 @ X8 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('155',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r1_waybel_0 @ X7 @ ( sk_F @ X10 @ X8 @ X7 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r2_hidden @ X10 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','155'])).

thf('157',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( sk_F @ sk_C @ X0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( m4_yellow_6 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_F @ sk_C @ sk_B @ sk_A ) )
      | ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('164',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X9 != X10 )
      | ~ ( v2_struct_0 @ ( sk_F @ X10 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('165',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( v2_struct_0 @ ( sk_F @ X10 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r2_hidden @ X10 @ ( a_2_1_yellow_6 @ X7 @ X8 ) )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ~ ( v2_struct_0 @ ( sk_F @ sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['163','165'])).

thf('167',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ~ ( v2_struct_0 @ ( sk_F @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( m4_yellow_6 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','168'])).

thf('170',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('176',plain,
    ( ( u1_struct_0 @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('177',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X3 @ X4 )
      | ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('180',plain,
    ( ( u1_pre_topc @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    = ( a_2_1_yellow_6 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ X0 @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','181'])).

thf('183',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(clc,[status(thm)],['174','182'])).

thf('184',plain,
    ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','87'])).

thf('185',plain,
    ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('187',plain,
    ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ~ ! [X16: $i,X17: $i] :
          ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
          | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
          | ~ ( l1_waybel_0 @ X17 @ sk_A )
          | ~ ( v7_waybel_0 @ X17 )
          | ~ ( v4_orders_2 @ X17 )
          | ( v2_struct_0 @ X17 )
          | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ sk_B )
        | ( r1_waybel_0 @ sk_A @ X17 @ sk_C )
        | ~ ( l1_waybel_0 @ X17 @ sk_A )
        | ~ ( v7_waybel_0 @ X17 )
        | ~ ( v4_orders_2 @ X17 )
        | ( v2_struct_0 @ X17 )
        | ~ ( r2_hidden @ X16 @ sk_C ) ) ),
    inference(split,[status(esa)],['47'])).

thf('189',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('190',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','9','11','13','59','187','188','189'])).

thf('191',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','190'])).

thf('192',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('193',plain,(
    r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','5','7','9','11','189','59','187','188','13'])).

thf('194',plain,(
    r2_hidden @ ( k4_tarski @ sk_E_1 @ sk_D_1 ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['47'])).

thf('196',plain,
    ( ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','181'])).

thf('197',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ( X9
        = ( sk_D @ X8 @ X7 @ X9 ) )
      | ~ ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('199',plain,
    ( ( ( sk_C
        = ( sk_D @ sk_B @ sk_A @ sk_C ) )
      | ~ ( m4_yellow_6 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( ( sk_C
        = ( sk_D @ sk_B @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( sk_C
      = ( sk_D @ sk_B @ sk_A @ sk_C ) )
   <= ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','9','11','189','13','59','187','188'])).

thf('206',plain,
    ( sk_C
    = ( sk_D @ sk_B @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['207'])).

thf('209',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['207'])).

thf('210',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','9','11','189','13','59','187','188','209'])).

thf('211',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['208','210'])).

thf('212',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m4_yellow_6 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X11 ) @ X8 )
      | ( r1_waybel_0 @ X7 @ X12 @ ( sk_D @ X8 @ X7 @ X9 ) )
      | ~ ( l1_waybel_0 @ X12 @ X7 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( r2_hidden @ X11 @ ( sk_D @ X8 @ X7 @ X9 ) )
      | ~ ( r2_hidden @ X9 @ ( a_2_1_yellow_6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow_6])).

thf('213',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_D_1 @ ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v7_waybel_0 @ X2 )
      | ~ ( l1_waybel_0 @ X2 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ X2 @ ( sk_D @ X0 @ sk_A @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ sk_D_1 ) @ X0 )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_D_1 @ ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v7_waybel_0 @ X2 )
      | ~ ( l1_waybel_0 @ X2 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ X2 @ ( sk_D @ X0 @ sk_A @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ sk_D_1 ) @ X0 )
      | ~ ( m4_yellow_6 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m4_yellow_6 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_D_1 ) @ sk_B )
      | ( r1_waybel_0 @ sk_A @ X0 @ ( sk_D @ sk_B @ sk_A @ sk_C ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['206','215'])).

thf('217',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('218',plain,(
    r2_hidden @ sk_D_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['5','7','9','11','189','13','59','187','188','3'])).

thf('219',plain,(
    r2_hidden @ sk_D_1 @ sk_C ),
    inference(simpl_trail,[status(thm)],['217','218'])).

thf('220',plain,(
    m4_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( sk_C
    = ( sk_D @ sk_B @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['204','205'])).

thf('222',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('223',plain,(
    v3_pre_topc @ sk_C @ ( k13_yellow_6 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','9','11','189','13','59','187','188'])).

thf('224',plain,(
    r2_hidden @ sk_C @ ( a_2_1_yellow_6 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_D_1 ) @ sk_B )
      | ( r1_waybel_0 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['216','219','220','221','224'])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_E_1 )
    | ~ ( v4_orders_2 @ sk_E_1 )
    | ~ ( v7_waybel_0 @ sk_E_1 )
    | ~ ( l1_waybel_0 @ sk_E_1 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['194','225'])).

thf('227',plain,
    ( ( v4_orders_2 @ sk_E_1 )
   <= ( v4_orders_2 @ sk_E_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('228',plain,(
    v4_orders_2 @ sk_E_1 ),
    inference('sat_resolution*',[status(thm)],['3','5','9','11','189','13','59','187','188','7'])).

thf('229',plain,(
    v4_orders_2 @ sk_E_1 ),
    inference(simpl_trail,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( v7_waybel_0 @ sk_E_1 )
   <= ( v7_waybel_0 @ sk_E_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('231',plain,(
    v7_waybel_0 @ sk_E_1 ),
    inference('sat_resolution*',[status(thm)],['3','5','7','11','189','13','59','187','188','9'])).

thf('232',plain,(
    v7_waybel_0 @ sk_E_1 ),
    inference(simpl_trail,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( l1_waybel_0 @ sk_E_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_E_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('234',plain,(
    l1_waybel_0 @ sk_E_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','5','7','9','189','13','59','187','188','11'])).

thf('235',plain,(
    l1_waybel_0 @ sk_E_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_E_1 )
    | ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['226','229','232','235'])).

thf('237',plain,
    ( ~ ( v2_struct_0 @ sk_E_1 )
   <= ~ ( v2_struct_0 @ sk_E_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_E_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','7','9','11','189','13','59','187','188','5'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_E_1 ) ),
    inference(simpl_trail,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ) ),
    inference(clc,[status(thm)],['236','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    r1_waybel_0 @ sk_A @ sk_E_1 @ sk_C ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['191','242'])).


%------------------------------------------------------------------------------
