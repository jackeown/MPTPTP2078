%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XbHAAkDkUZ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 159 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  484 (2745 expanded)
%              Number of equality atoms :    9 ( 117 expanded)
%              Maximal formula depth    :   22 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(t20_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_yellow_6 @ C @ A @ B )
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
                                  & ( r1_orders_2 @ C @ F @ G ) )
                               => ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_waybel_0 @ B @ A )
           => ! [C: $i] :
                ( ( m1_yellow_6 @ C @ A @ B )
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
                                    & ( r1_orders_2 @ C @ F @ G ) )
                                 => ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_yellow_6])).

thf('0',plain,(
    ~ ( r1_orders_2 @ sk_B @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( u1_orders_2 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D @ X0 ) @ ( u1_orders_2 @ sk_C_1 ) )
      | ~ ( r1_orders_2 @ sk_C_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_yellow_6 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( l1_waybel_0 @ X16 @ X14 )
      | ~ ( m1_yellow_6 @ X16 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('11',plain,
    ( ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_waybel_0 @ X9 @ X10 )
      | ( l1_orders_2 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('16',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D @ X0 ) @ ( u1_orders_2 @ sk_C_1 ) )
      | ~ ( r1_orders_2 @ sk_C_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['8','18'])).

thf('20',plain,
    ( ~ ( r1_orders_2 @ sk_C_1 @ sk_D @ sk_E )
    | ( r2_hidden @ ( k4_tarski @ sk_D @ sk_E ) @ ( u1_orders_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    r1_orders_2 @ sk_C_1 @ sk_F @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_orders_2 @ sk_C_1 @ sk_D @ sk_E ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ sk_D @ sk_E ) @ ( u1_orders_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['20','24'])).

thf('26',plain,(
    m1_yellow_6 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( l1_waybel_0 @ C @ A )
             => ( ( m1_yellow_6 @ C @ A @ B )
              <=> ( ( m1_yellow_0 @ C @ B )
                  & ( ( u1_waybel_0 @ A @ C )
                    = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_waybel_0 @ X11 @ X12 )
      | ~ ( m1_yellow_6 @ X13 @ X12 @ X11 )
      | ( m1_yellow_0 @ X13 @ X11 )
      | ~ ( l1_waybel_0 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('28',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ( m1_yellow_0 @ sk_C_1 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('31',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_yellow_0 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_yellow_0 @ X7 @ X8 )
      | ( r1_tarski @ ( u1_orders_2 @ X7 ) @ ( u1_orders_2 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('34',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_waybel_0 @ X9 @ X10 )
      | ( l1_orders_2 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('37',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_B ) ),
    inference(demod,[status(thm)],['34','39','40'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ sk_D @ sk_E ) @ ( u1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( u1_orders_2 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('46',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_orders_2 @ sk_B @ sk_D @ sk_E )
    | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_orders_2 @ sk_B @ sk_D @ sk_E ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XbHAAkDkUZ
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:18:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 50 iterations in 0.024s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.22/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.49  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.22/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.49  thf(t20_yellow_6, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_waybel_0 @ B @ A ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.22/0.49               ( ![D:$i]:
% 0.22/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.49                   ( ![E:$i]:
% 0.22/0.49                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.49                       ( ![F:$i]:
% 0.22/0.49                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.49                           ( ![G:$i]:
% 0.22/0.49                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.49                               ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.22/0.49                                   ( r1_orders_2 @ C @ F @ G ) ) =>
% 0.22/0.49                                 ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( l1_struct_0 @ A ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( l1_waybel_0 @ B @ A ) =>
% 0.22/0.49              ( ![C:$i]:
% 0.22/0.49                ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.22/0.49                  ( ![D:$i]:
% 0.22/0.49                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.49                      ( ![E:$i]:
% 0.22/0.49                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.49                          ( ![F:$i]:
% 0.22/0.49                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.49                              ( ![G:$i]:
% 0.22/0.49                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.49                                  ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.22/0.49                                      ( r1_orders_2 @ C @ F @ G ) ) =>
% 0.22/0.49                                    ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t20_yellow_6])).
% 0.22/0.49  thf('0', plain, (~ (r1_orders_2 @ sk_B @ sk_D @ sk_E)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('2', plain, (((sk_E) = (sk_G))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('5', plain, (((sk_D) = (sk_F))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf(d9_orders_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_orders_2 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.22/0.49                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ~ (r1_orders_2 @ X5 @ X4 @ X6)
% 0.22/0.49          | (r2_hidden @ (k4_tarski @ X4 @ X6) @ (u1_orders_2 @ X5))
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ~ (l1_orders_2 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_orders_2 @ sk_C_1)
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.49          | (r2_hidden @ (k4_tarski @ sk_D @ X0) @ (u1_orders_2 @ sk_C_1))
% 0.22/0.49          | ~ (r1_orders_2 @ sk_C_1 @ sk_D @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain, ((m1_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_m1_yellow_6, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.49       ( ![C:$i]: ( ( m1_yellow_6 @ C @ A @ B ) => ( l1_waybel_0 @ C @ A ) ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X14)
% 0.22/0.49          | ~ (l1_waybel_0 @ X15 @ X14)
% 0.22/0.49          | (l1_waybel_0 @ X16 @ X14)
% 0.22/0.49          | ~ (m1_yellow_6 @ X16 @ X14 @ X15))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (((l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.22/0.49        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.22/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('14', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.49  thf(dt_l1_waybel_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) =>
% 0.22/0.49       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         (~ (l1_waybel_0 @ X9 @ X10)
% 0.22/0.49          | (l1_orders_2 @ X9)
% 0.22/0.49          | ~ (l1_struct_0 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.22/0.49  thf('16', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain, ((l1_orders_2 @ sk_C_1)),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.49          | (r2_hidden @ (k4_tarski @ sk_D @ X0) @ (u1_orders_2 @ sk_C_1))
% 0.22/0.49          | ~ (r1_orders_2 @ sk_C_1 @ sk_D @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((~ (r1_orders_2 @ sk_C_1 @ sk_D @ sk_E)
% 0.22/0.49        | (r2_hidden @ (k4_tarski @ sk_D @ sk_E) @ (u1_orders_2 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '19'])).
% 0.22/0.49  thf('21', plain, ((r1_orders_2 @ sk_C_1 @ sk_F @ sk_G)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain, (((sk_D) = (sk_F))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain, (((sk_E) = (sk_G))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain, ((r1_orders_2 @ sk_C_1 @ sk_D @ sk_E)),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((r2_hidden @ (k4_tarski @ sk_D @ sk_E) @ (u1_orders_2 @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '24'])).
% 0.22/0.49  thf('26', plain, ((m1_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d8_yellow_6, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_waybel_0 @ B @ A ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( l1_waybel_0 @ C @ A ) =>
% 0.22/0.49               ( ( m1_yellow_6 @ C @ A @ B ) <=>
% 0.22/0.49                 ( ( m1_yellow_0 @ C @ B ) & 
% 0.22/0.49                   ( ( u1_waybel_0 @ A @ C ) =
% 0.22/0.49                     ( k2_partfun1 @
% 0.22/0.49                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.49                       ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.49         (~ (l1_waybel_0 @ X11 @ X12)
% 0.22/0.49          | ~ (m1_yellow_6 @ X13 @ X12 @ X11)
% 0.22/0.49          | (m1_yellow_0 @ X13 @ X11)
% 0.22/0.49          | ~ (l1_waybel_0 @ X13 @ X12)
% 0.22/0.49          | ~ (l1_struct_0 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      ((~ (l1_struct_0 @ sk_A)
% 0.22/0.49        | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.22/0.49        | (m1_yellow_0 @ sk_C_1 @ sk_B)
% 0.22/0.49        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.49  thf('31', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain, ((m1_yellow_0 @ sk_C_1 @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.22/0.49  thf(d13_yellow_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_orders_2 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_orders_2 @ B ) =>
% 0.22/0.49           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.22/0.49             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.49               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (l1_orders_2 @ X7)
% 0.22/0.49          | ~ (m1_yellow_0 @ X7 @ X8)
% 0.22/0.49          | (r1_tarski @ (u1_orders_2 @ X7) @ (u1_orders_2 @ X8))
% 0.22/0.49          | ~ (l1_orders_2 @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((~ (l1_orders_2 @ sk_B)
% 0.22/0.49        | (r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_B))
% 0.22/0.49        | ~ (l1_orders_2 @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf('35', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         (~ (l1_waybel_0 @ X9 @ X10)
% 0.22/0.49          | (l1_orders_2 @ X9)
% 0.22/0.49          | ~ (l1_struct_0 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.22/0.49  thf('37', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('39', plain, ((l1_orders_2 @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.49  thf('40', plain, ((l1_orders_2 @ sk_C_1)),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      ((r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['34', '39', '40'])).
% 0.22/0.49  thf(d3_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.49          | (r2_hidden @ X0 @ X2)
% 0.22/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ X0 @ (u1_orders_2 @ sk_B))
% 0.22/0.49          | ~ (r2_hidden @ X0 @ (u1_orders_2 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      ((r2_hidden @ (k4_tarski @ sk_D @ sk_E) @ (u1_orders_2 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['25', '43'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (u1_orders_2 @ X5))
% 0.22/0.49          | (r1_orders_2 @ X5 @ X4 @ X6)
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ~ (l1_orders_2 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      ((~ (l1_orders_2 @ sk_B)
% 0.22/0.49        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.22/0.49        | (r1_orders_2 @ sk_B @ sk_D @ sk_E)
% 0.22/0.49        | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.49  thf('47', plain, ((l1_orders_2 @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.49  thf('48', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('49', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('50', plain, ((r1_orders_2 @ sk_B @ sk_D @ sk_E)),
% 0.22/0.49      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.22/0.49  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
