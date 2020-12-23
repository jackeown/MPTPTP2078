%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9eKerTriB9

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 175 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  689 (3610 expanded)
%              Number of equality atoms :   14 ( 135 expanded)
%              Maximal formula depth    :   22 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_yellow_6_type,type,(
    v2_yellow_6: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('1',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t21_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v2_yellow_6 @ C @ A @ B )
                & ( m1_yellow_6 @ C @ A @ B ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                             => ( ( ( D = F )
                                  & ( E = G )
                                  & ( r1_orders_2 @ B @ D @ E ) )
                               => ( r1_orders_2 @ C @ F @ G ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v2_yellow_6 @ C @ A @ B )
                  & ( m1_yellow_6 @ C @ A @ B ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( D = F )
                                    & ( E = G )
                                    & ( r1_orders_2 @ B @ D @ E ) )
                                 => ( r1_orders_2 @ C @ F @ G ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_yellow_6])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v4_yellow_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ( ( ( E = C )
                              & ( F = D )
                              & ( r1_orders_2 @ A @ C @ D )
                              & ( r2_hidden @ E @ ( u1_struct_0 @ B ) ) )
                           => ( r1_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v4_yellow_0 @ X5 @ X6 )
      | ~ ( m1_yellow_0 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X9 @ X8 )
      | ( X8 != X7 )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X6 @ X10 @ X7 )
      | ( X9 != X10 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_yellow_0])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X6 @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X10 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_yellow_0 @ X5 @ X6 )
      | ~ ( v4_yellow_0 @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_yellow_0 @ X0 @ sk_B )
      | ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D @ X1 )
      | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_waybel_0 @ X11 @ X12 )
      | ( l1_orders_2 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('16',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_yellow_0 @ X0 @ sk_B )
      | ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D @ X1 )
      | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_B @ sk_D @ sk_E )
      | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( v4_yellow_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    r1_orders_2 @ sk_B @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( v4_yellow_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v4_yellow_0 @ sk_C @ sk_B )
    | ~ ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    | ( r1_orders_2 @ sk_C @ sk_D @ sk_E )
    | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','22'])).

thf('24',plain,(
    v2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_yellow_6 @ C @ A @ B )
             => ( ( v2_yellow_6 @ C @ A @ B )
              <=> ( ( v4_yellow_0 @ C @ B )
                  & ( m1_yellow_0 @ C @ B ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( v2_yellow_6 @ X15 @ X14 @ X13 )
      | ( v4_yellow_0 @ X15 @ X13 )
      | ~ ( m1_yellow_6 @ X15 @ X14 @ X13 )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_6])).

thf('26',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( m1_yellow_6 @ sk_C @ sk_A @ sk_B )
    | ( v4_yellow_0 @ sk_C @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_yellow_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    v2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( v2_yellow_6 @ X15 @ X14 @ X13 )
      | ( m1_yellow_0 @ X15 @ X13 )
      | ~ ( m1_yellow_6 @ X15 @ X14 @ X13 )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_6])).

thf('33',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( m1_yellow_6 @ sk_C @ sk_A @ sk_B )
    | ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_orders_2 @ sk_C @ sk_D @ sk_E )
    | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','30','37','40'])).

thf('42',plain,(
    ~ ( r1_orders_2 @ sk_C @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( r1_orders_2 @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','45'])).

thf('47',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','47'])).

thf('49',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','48'])).

thf('50',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( l1_waybel_0 @ X18 @ X16 )
      | ~ ( m1_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('52',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_waybel_0 @ X11 @ X12 )
      | ( l1_orders_2 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('57',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','59'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('61',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ~ ( l1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['57','58'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9eKerTriB9
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 66 iterations in 0.030s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(v4_yellow_0_type, type, v4_yellow_0: $i > $i > $o).
% 0.19/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.48  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.19/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.48  thf(v2_yellow_6_type, type, v2_yellow_6: $i > $i > $i > $o).
% 0.19/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.48  thf(dt_l1_orders_2, axiom,
% 0.19/0.48    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.48  thf('0', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_orders_2 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.19/0.48  thf('1', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_orders_2 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.19/0.48  thf(d3_struct_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X2 : $i]:
% 0.19/0.48         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.48  thf(t21_yellow_6, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_struct_0 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_yellow_6 @ C @ A @ B ) & 
% 0.19/0.48                 ( m1_yellow_6 @ C @ A @ B ) ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48                   ( ![E:$i]:
% 0.19/0.48                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48                       ( ![F:$i]:
% 0.19/0.48                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.48                           ( ![G:$i]:
% 0.19/0.48                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.48                               ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.19/0.48                                   ( r1_orders_2 @ B @ D @ E ) ) =>
% 0.19/0.48                                 ( r1_orders_2 @ C @ F @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( l1_struct_0 @ A ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_yellow_6 @ C @ A @ B ) & 
% 0.19/0.48                    ( m1_yellow_6 @ C @ A @ B ) ) =>
% 0.19/0.48                  ( ![D:$i]:
% 0.19/0.48                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48                      ( ![E:$i]:
% 0.19/0.48                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48                          ( ![F:$i]:
% 0.19/0.48                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.48                              ( ![G:$i]:
% 0.19/0.48                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.48                                  ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.19/0.48                                      ( r1_orders_2 @ B @ D @ E ) ) =>
% 0.19/0.48                                    ( r1_orders_2 @ C @ F @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t21_yellow_6])).
% 0.19/0.48  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('4', plain, (((sk_D) = (sk_F))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('5', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(t2_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ X0 @ X1)
% 0.19/0.48          | (v1_xboole_0 @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.48        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('9', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t61_yellow_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_orders_2 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( v4_yellow_0 @ B @ A ) & ( m1_yellow_0 @ B @ A ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48                   ( ![E:$i]:
% 0.19/0.48                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48                       ( ![F:$i]:
% 0.19/0.48                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48                           ( ( ( ( E ) = ( C ) ) & ( ( F ) = ( D ) ) & 
% 0.19/0.48                               ( r1_orders_2 @ A @ C @ D ) & 
% 0.19/0.48                               ( r2_hidden @ E @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.48                             ( r1_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (~ (v4_yellow_0 @ X5 @ X6)
% 0.19/0.48          | ~ (m1_yellow_0 @ X5 @ X6)
% 0.19/0.48          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.19/0.48          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X5))
% 0.19/0.48          | (r1_orders_2 @ X5 @ X9 @ X8)
% 0.19/0.48          | ((X8) != (X7))
% 0.19/0.48          | ~ (r2_hidden @ X9 @ (u1_struct_0 @ X5))
% 0.19/0.48          | ~ (r1_orders_2 @ X6 @ X10 @ X7)
% 0.19/0.48          | ((X9) != (X10))
% 0.19/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X5))
% 0.19/0.48          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X6))
% 0.19/0.48          | ~ (l1_orders_2 @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [t61_yellow_0])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i, X7 : $i, X10 : $i]:
% 0.19/0.48         (~ (l1_orders_2 @ X6)
% 0.19/0.48          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X6))
% 0.19/0.48          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X5))
% 0.19/0.48          | ~ (r1_orders_2 @ X6 @ X10 @ X7)
% 0.19/0.48          | ~ (r2_hidden @ X10 @ (u1_struct_0 @ X5))
% 0.19/0.48          | (r1_orders_2 @ X5 @ X10 @ X7)
% 0.19/0.48          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.19/0.48          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.19/0.48          | ~ (m1_yellow_0 @ X5 @ X6)
% 0.19/0.48          | ~ (v4_yellow_0 @ X5 @ X6))),
% 0.19/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v4_yellow_0 @ X0 @ sk_B)
% 0.19/0.48          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.48          | (r1_orders_2 @ X0 @ sk_D @ X1)
% 0.19/0.48          | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.48          | ~ (r1_orders_2 @ sk_B @ sk_D @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.48          | ~ (l1_orders_2 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '12'])).
% 0.19/0.48  thf('14', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_l1_waybel_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_struct_0 @ A ) =>
% 0.19/0.48       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (l1_waybel_0 @ X11 @ X12)
% 0.19/0.48          | (l1_orders_2 @ X11)
% 0.19/0.48          | ~ (l1_struct_0 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.19/0.48  thf('16', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain, ((l1_orders_2 @ sk_B)),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v4_yellow_0 @ X0 @ sk_B)
% 0.19/0.48          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.48          | (r1_orders_2 @ X0 @ sk_D @ X1)
% 0.19/0.48          | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.48          | ~ (r1_orders_2 @ sk_B @ sk_D @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.48          | ~ (r1_orders_2 @ sk_B @ sk_D @ sk_E)
% 0.19/0.48          | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.48          | (r1_orders_2 @ X0 @ sk_D @ sk_E)
% 0.19/0.48          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.19/0.48          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.19/0.48          | ~ (v4_yellow_0 @ X0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '19'])).
% 0.19/0.48  thf('21', plain, ((r1_orders_2 @ sk_B @ sk_D @ sk_E)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.48          | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.48          | (r1_orders_2 @ X0 @ sk_D @ sk_E)
% 0.19/0.48          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.19/0.48          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.19/0.48          | ~ (v4_yellow_0 @ X0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((~ (v4_yellow_0 @ sk_C @ sk_B)
% 0.19/0.48        | ~ (m1_yellow_0 @ sk_C @ sk_B)
% 0.19/0.48        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C))
% 0.19/0.48        | (r1_orders_2 @ sk_C @ sk_D @ sk_E)
% 0.19/0.48        | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '22'])).
% 0.19/0.48  thf('24', plain, ((v2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d9_yellow_6, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_struct_0 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( l1_waybel_0 @ B @ A ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.19/0.48               ( ( v2_yellow_6 @ C @ A @ B ) <=>
% 0.19/0.48                 ( ( v4_yellow_0 @ C @ B ) & ( m1_yellow_0 @ C @ B ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.48         (~ (l1_waybel_0 @ X13 @ X14)
% 0.19/0.48          | ~ (v2_yellow_6 @ X15 @ X14 @ X13)
% 0.19/0.48          | (v4_yellow_0 @ X15 @ X13)
% 0.19/0.48          | ~ (m1_yellow_6 @ X15 @ X14 @ X13)
% 0.19/0.48          | ~ (l1_struct_0 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [d9_yellow_6])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | ~ (m1_yellow_6 @ sk_C @ sk_A @ sk_B)
% 0.19/0.48        | (v4_yellow_0 @ sk_C @ sk_B)
% 0.19/0.48        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('28', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('29', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('30', plain, ((v4_yellow_0 @ sk_C @ sk_B)),
% 0.19/0.48      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.19/0.48  thf('31', plain, ((v2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.48         (~ (l1_waybel_0 @ X13 @ X14)
% 0.19/0.48          | ~ (v2_yellow_6 @ X15 @ X14 @ X13)
% 0.19/0.48          | (m1_yellow_0 @ X15 @ X13)
% 0.19/0.48          | ~ (m1_yellow_6 @ X15 @ X14 @ X13)
% 0.19/0.48          | ~ (l1_struct_0 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [d9_yellow_6])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | ~ (m1_yellow_6 @ sk_C @ sk_A @ sk_B)
% 0.19/0.48        | (m1_yellow_0 @ sk_C @ sk_B)
% 0.19/0.48        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('35', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('36', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('37', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.19/0.48      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.19/0.48  thf('38', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('39', plain, (((sk_E) = (sk_G))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('40', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (((r1_orders_2 @ sk_C @ sk_D @ sk_E)
% 0.19/0.48        | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['23', '30', '37', '40'])).
% 0.19/0.48  thf('42', plain, (~ (r1_orders_2 @ sk_C @ sk_F @ sk_G)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('43', plain, (((sk_D) = (sk_F))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('44', plain, (((sk_E) = (sk_G))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('45', plain, (~ (r1_orders_2 @ sk_C @ sk_D @ sk_E)),
% 0.19/0.48      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.19/0.48  thf('46', plain, (~ (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('clc', [status(thm)], ['41', '45'])).
% 0.19/0.48  thf('47', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '46'])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.19/0.48      inference('sup+', [status(thm)], ['2', '47'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      ((~ (l1_orders_2 @ sk_C) | (v1_xboole_0 @ (k2_struct_0 @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '48'])).
% 0.19/0.48  thf('50', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_m1_yellow_6, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48       ( ![C:$i]: ( ( m1_yellow_6 @ C @ A @ B ) => ( l1_waybel_0 @ C @ A ) ) ) ))).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.48         (~ (l1_struct_0 @ X16)
% 0.19/0.48          | ~ (l1_waybel_0 @ X17 @ X16)
% 0.19/0.48          | (l1_waybel_0 @ X18 @ X16)
% 0.19/0.48          | ~ (m1_yellow_6 @ X18 @ X16 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      (((l1_waybel_0 @ sk_C @ sk_A)
% 0.19/0.48        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.48  thf('53', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('55', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.19/0.48      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (l1_waybel_0 @ X11 @ X12)
% 0.19/0.48          | (l1_orders_2 @ X11)
% 0.19/0.48          | ~ (l1_struct_0 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.19/0.48  thf('57', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.48  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('59', plain, ((l1_orders_2 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.48  thf('60', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['49', '59'])).
% 0.19/0.48  thf(fc5_struct_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.19/0.48  thf('61', plain,
% 0.19/0.48      (![X3 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ (k2_struct_0 @ X3))
% 0.19/0.48          | ~ (l1_struct_0 @ X3)
% 0.19/0.48          | (v2_struct_0 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.19/0.48  thf('62', plain, (((v2_struct_0 @ sk_C) | ~ (l1_struct_0 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.48  thf('63', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('64', plain, (~ (l1_struct_0 @ sk_C)),
% 0.19/0.48      inference('clc', [status(thm)], ['62', '63'])).
% 0.19/0.48  thf('65', plain, (~ (l1_orders_2 @ sk_C)),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '64'])).
% 0.19/0.48  thf('66', plain, ((l1_orders_2 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.48  thf('67', plain, ($false), inference('demod', [status(thm)], ['65', '66'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
