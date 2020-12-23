%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hiJx7zi9Zw

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 147 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  656 (3133 expanded)
%              Number of equality atoms :   12 ( 117 expanded)
%              Maximal formula depth    :   22 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_yellow_6_type,type,(
    v2_yellow_6: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

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

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( v4_yellow_0 @ X4 @ X5 )
      | ~ ( m1_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X8 @ X7 )
      | ( X7 != X6 )
      | ~ ( r2_hidden @ X8 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X5 @ X9 @ X6 )
      | ( X8 != X9 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_yellow_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X5 @ X9 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X9 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_yellow_0 @ X4 @ X5 )
      | ~ ( v4_yellow_0 @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( l1_orders_2 @ X10 )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('14',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_yellow_0 @ X0 @ sk_B )
      | ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D @ X1 )
      | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_B @ sk_D @ sk_E )
      | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( v4_yellow_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    r1_orders_2 @ sk_B @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( v4_yellow_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v4_yellow_0 @ sk_C @ sk_B )
    | ~ ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    | ( r1_orders_2 @ sk_C @ sk_D @ sk_E )
    | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v2_yellow_6 @ X14 @ X13 @ X12 )
      | ( v4_yellow_0 @ X14 @ X12 )
      | ~ ( m1_yellow_6 @ X14 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_6])).

thf('24',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( m1_yellow_6 @ sk_C @ sk_A @ sk_B )
    | ( v4_yellow_0 @ sk_C @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v4_yellow_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    v2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v2_yellow_6 @ X14 @ X13 @ X12 )
      | ( m1_yellow_0 @ X14 @ X12 )
      | ~ ( m1_yellow_6 @ X14 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_6])).

thf('31',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( m1_yellow_6 @ sk_C @ sk_A @ sk_B )
    | ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_orders_2 @ sk_C @ sk_D @ sk_E )
    | ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','28','35','38'])).

thf('40',plain,(
    ~ ( r1_orders_2 @ sk_C @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( r1_orders_2 @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['39','43'])).

thf('45',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( l1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( l1_waybel_0 @ X17 @ X15 )
      | ~ ( m1_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('53',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( l1_orders_2 @ X10 )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('58',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['50','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hiJx7zi9Zw
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 36 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.21/0.47  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.47  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.47  thf(v4_yellow_0_type, type, v4_yellow_0: $i > $i > $o).
% 0.21/0.47  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.47  thf(v2_yellow_6_type, type, v2_yellow_6: $i > $i > $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(dt_l1_orders_2, axiom,
% 0.21/0.47    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.47  thf('0', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.47  thf(t21_yellow_6, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_yellow_6 @ C @ A @ B ) & 
% 0.21/0.47                 ( m1_yellow_6 @ C @ A @ B ) ) =>
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                   ( ![E:$i]:
% 0.21/0.47                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                       ( ![F:$i]:
% 0.21/0.47                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.47                           ( ![G:$i]:
% 0.21/0.47                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.47                               ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.21/0.47                                   ( r1_orders_2 @ B @ D @ E ) ) =>
% 0.21/0.47                                 ( r1_orders_2 @ C @ F @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( l1_struct_0 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_yellow_6 @ C @ A @ B ) & 
% 0.21/0.47                    ( m1_yellow_6 @ C @ A @ B ) ) =>
% 0.21/0.47                  ( ![D:$i]:
% 0.21/0.47                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                      ( ![E:$i]:
% 0.21/0.47                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                          ( ![F:$i]:
% 0.21/0.47                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.47                              ( ![G:$i]:
% 0.21/0.47                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.47                                  ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.21/0.47                                      ( r1_orders_2 @ B @ D @ E ) ) =>
% 0.21/0.47                                    ( r1_orders_2 @ C @ F @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t21_yellow_6])).
% 0.21/0.47  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('2', plain, (((sk_D) = (sk_F))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t2_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ X1)
% 0.21/0.47          | (v1_xboole_0 @ X1)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.47        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('7', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t61_yellow_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( v4_yellow_0 @ B @ A ) & ( m1_yellow_0 @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47                   ( ![E:$i]:
% 0.21/0.47                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                       ( ![F:$i]:
% 0.21/0.47                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                           ( ( ( ( E ) = ( C ) ) & ( ( F ) = ( D ) ) & 
% 0.21/0.47                               ( r1_orders_2 @ A @ C @ D ) & 
% 0.21/0.47                               ( r2_hidden @ E @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.47                             ( r1_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (v4_yellow_0 @ X4 @ X5)
% 0.21/0.47          | ~ (m1_yellow_0 @ X4 @ X5)
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.47          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.21/0.47          | (r1_orders_2 @ X4 @ X8 @ X7)
% 0.21/0.47          | ((X7) != (X6))
% 0.21/0.47          | ~ (r2_hidden @ X8 @ (u1_struct_0 @ X4))
% 0.21/0.47          | ~ (r1_orders_2 @ X5 @ X9 @ X6)
% 0.21/0.47          | ((X8) != (X9))
% 0.21/0.47          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X4))
% 0.21/0.47          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X5))
% 0.21/0.47          | ~ (l1_orders_2 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t61_yellow_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X5)
% 0.21/0.47          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X5))
% 0.21/0.47          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X4))
% 0.21/0.47          | ~ (r1_orders_2 @ X5 @ X9 @ X6)
% 0.21/0.47          | ~ (r2_hidden @ X9 @ (u1_struct_0 @ X4))
% 0.21/0.47          | (r1_orders_2 @ X4 @ X9 @ X6)
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.47          | ~ (m1_yellow_0 @ X4 @ X5)
% 0.21/0.47          | ~ (v4_yellow_0 @ X4 @ X5))),
% 0.21/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v4_yellow_0 @ X0 @ sk_B)
% 0.21/0.47          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | (r1_orders_2 @ X0 @ sk_D @ X1)
% 0.21/0.47          | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (r1_orders_2 @ sk_B @ sk_D @ X1)
% 0.21/0.47          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (l1_orders_2 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.47  thf('12', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_l1_waybel_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) =>
% 0.21/0.47       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (l1_waybel_0 @ X10 @ X11)
% 0.21/0.47          | (l1_orders_2 @ X10)
% 0.21/0.47          | ~ (l1_struct_0 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.47  thf('14', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v4_yellow_0 @ X0 @ sk_B)
% 0.21/0.47          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | (r1_orders_2 @ X0 @ sk_D @ X1)
% 0.21/0.47          | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (r1_orders_2 @ sk_B @ sk_D @ X1)
% 0.21/0.47          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (r1_orders_2 @ sk_B @ sk_D @ sk_E)
% 0.21/0.47          | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.47          | (r1_orders_2 @ X0 @ sk_D @ sk_E)
% 0.21/0.47          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.21/0.47          | ~ (v4_yellow_0 @ X0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '17'])).
% 0.21/0.47  thf('19', plain, ((r1_orders_2 @ sk_B @ sk_D @ sk_E)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.47          | (r1_orders_2 @ X0 @ sk_D @ sk_E)
% 0.21/0.47          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.21/0.47          | ~ (v4_yellow_0 @ X0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((~ (v4_yellow_0 @ sk_C @ sk_B)
% 0.21/0.47        | ~ (m1_yellow_0 @ sk_C @ sk_B)
% 0.21/0.47        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C))
% 0.21/0.47        | (r1_orders_2 @ sk_C @ sk_D @ sk_E)
% 0.21/0.47        | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '20'])).
% 0.21/0.47  thf('22', plain, ((v2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d9_yellow_6, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.21/0.47               ( ( v2_yellow_6 @ C @ A @ B ) <=>
% 0.21/0.47                 ( ( v4_yellow_0 @ C @ B ) & ( m1_yellow_0 @ C @ B ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.47          | ~ (v2_yellow_6 @ X14 @ X13 @ X12)
% 0.21/0.47          | (v4_yellow_0 @ X14 @ X12)
% 0.21/0.47          | ~ (m1_yellow_6 @ X14 @ X13 @ X12)
% 0.21/0.47          | ~ (l1_struct_0 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_yellow_6])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.47        | ~ (m1_yellow_6 @ sk_C @ sk_A @ sk_B)
% 0.21/0.47        | (v4_yellow_0 @ sk_C @ sk_B)
% 0.21/0.47        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('28', plain, ((v4_yellow_0 @ sk_C @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.21/0.47  thf('29', plain, ((v2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.47          | ~ (v2_yellow_6 @ X14 @ X13 @ X12)
% 0.21/0.47          | (m1_yellow_0 @ X14 @ X12)
% 0.21/0.47          | ~ (m1_yellow_6 @ X14 @ X13 @ X12)
% 0.21/0.47          | ~ (l1_struct_0 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_yellow_6])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.47        | ~ (m1_yellow_6 @ sk_C @ sk_A @ sk_B)
% 0.21/0.47        | (m1_yellow_0 @ sk_C @ sk_B)
% 0.21/0.47        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('33', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('34', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('35', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.21/0.47  thf('36', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('37', plain, (((sk_E) = (sk_G))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('38', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (((r1_orders_2 @ sk_C @ sk_D @ sk_E)
% 0.21/0.47        | ~ (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['21', '28', '35', '38'])).
% 0.21/0.47  thf('40', plain, (~ (r1_orders_2 @ sk_C @ sk_F @ sk_G)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('41', plain, (((sk_D) = (sk_F))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('42', plain, (((sk_E) = (sk_G))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('43', plain, (~ (r1_orders_2 @ sk_C @ sk_D @ sk_E)),
% 0.21/0.47      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.47  thf('44', plain, (~ (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('clc', [status(thm)], ['39', '43'])).
% 0.21/0.47  thf('45', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '44'])).
% 0.21/0.47  thf(fc2_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      (![X2 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.21/0.47          | ~ (l1_struct_0 @ X2)
% 0.21/0.47          | (v2_struct_0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.47  thf('47', plain, (((v2_struct_0 @ sk_C) | ~ (l1_struct_0 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.47  thf('48', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('49', plain, (~ (l1_struct_0 @ sk_C)),
% 0.21/0.47      inference('clc', [status(thm)], ['47', '48'])).
% 0.21/0.47  thf('50', plain, (~ (l1_orders_2 @ sk_C)),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '49'])).
% 0.21/0.47  thf('51', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_m1_yellow_6, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.47       ( ![C:$i]: ( ( m1_yellow_6 @ C @ A @ B ) => ( l1_waybel_0 @ C @ A ) ) ) ))).
% 0.21/0.47  thf('52', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.47         (~ (l1_struct_0 @ X15)
% 0.21/0.47          | ~ (l1_waybel_0 @ X16 @ X15)
% 0.21/0.47          | (l1_waybel_0 @ X17 @ X15)
% 0.21/0.47          | ~ (m1_yellow_6 @ X17 @ X15 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      (((l1_waybel_0 @ sk_C @ sk_A)
% 0.21/0.47        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.47  thf('54', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('56', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.21/0.47  thf('57', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (l1_waybel_0 @ X10 @ X11)
% 0.21/0.47          | (l1_orders_2 @ X10)
% 0.21/0.47          | ~ (l1_struct_0 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.47  thf('58', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.47  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('60', plain, ((l1_orders_2 @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.47  thf('61', plain, ($false), inference('demod', [status(thm)], ['50', '60'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
