%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UXGXBkGPbB

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (  95 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  448 (1774 expanded)
%              Number of equality atoms :   13 (  81 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

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
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
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
                              & ( r1_orders_2 @ B @ E @ F ) )
                           => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ X4 @ X3 )
      | ( X3 != X2 )
      | ( r1_orders_2 @ X1 @ X5 @ X2 )
      | ( X4 != X5 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t60_yellow_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X1 @ X5 @ X2 )
      | ~ ( r1_orders_2 @ X0 @ X5 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_yellow_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ sk_D @ X1 )
      | ( r1_orders_2 @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_waybel_0 @ X6 @ X7 )
      | ( l1_orders_2 @ X6 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('11',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ sk_D @ X1 )
      | ( r1_orders_2 @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ sk_B @ sk_D @ sk_E )
      | ~ ( r1_orders_2 @ X0 @ sk_D @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_yellow_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,
    ( ~ ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_C @ sk_D @ sk_E )
    | ( r1_orders_2 @ sk_B @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
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

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( m1_yellow_6 @ X10 @ X9 @ X8 )
      | ( m1_yellow_0 @ X10 @ X8 )
      | ~ ( l1_waybel_0 @ X10 @ X9 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('19',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ( l1_waybel_0 @ X13 @ X11 )
      | ~ ( m1_yellow_6 @ X13 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('23',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['19','20','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_orders_2 @ sk_C @ sk_F @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_orders_2 @ sk_C @ sk_D @ sk_E ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    r1_orders_2 @ sk_B @ sk_D @ sk_E ),
    inference(demod,[status(thm)],['16','28','31','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UXGXBkGPbB
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 23 iterations in 0.015s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.19/0.46  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.46  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.19/0.46  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.46  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.19/0.46  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.46  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.19/0.46  thf(t20_yellow_6, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_struct_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( l1_waybel_0 @ B @ A ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.19/0.46               ( ![D:$i]:
% 0.19/0.46                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.46                   ( ![E:$i]:
% 0.19/0.46                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.46                       ( ![F:$i]:
% 0.19/0.46                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.46                           ( ![G:$i]:
% 0.19/0.46                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.46                               ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.19/0.46                                   ( r1_orders_2 @ C @ F @ G ) ) =>
% 0.19/0.46                                 ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( l1_struct_0 @ A ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( l1_waybel_0 @ B @ A ) =>
% 0.19/0.46              ( ![C:$i]:
% 0.19/0.46                ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.19/0.46                  ( ![D:$i]:
% 0.19/0.46                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.46                      ( ![E:$i]:
% 0.19/0.46                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.46                          ( ![F:$i]:
% 0.19/0.46                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.46                              ( ![G:$i]:
% 0.19/0.46                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.46                                  ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.19/0.46                                      ( r1_orders_2 @ C @ F @ G ) ) =>
% 0.19/0.46                                    ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t20_yellow_6])).
% 0.19/0.46  thf('0', plain, (~ (r1_orders_2 @ sk_B @ sk_D @ sk_E)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('2', plain, (((sk_D) = (sk_F))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t60_yellow_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_orders_2 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_yellow_0 @ B @ A ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.46               ( ![D:$i]:
% 0.19/0.46                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.46                   ( ![E:$i]:
% 0.19/0.46                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.46                       ( ![F:$i]:
% 0.19/0.46                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.46                           ( ( ( ( E ) = ( C ) ) & ( ( F ) = ( D ) ) & 
% 0.19/0.46                               ( r1_orders_2 @ B @ E @ F ) ) =>
% 0.19/0.46                             ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.46         (~ (m1_yellow_0 @ X0 @ X1)
% 0.19/0.46          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.19/0.46          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.19/0.46          | ~ (r1_orders_2 @ X0 @ X4 @ X3)
% 0.19/0.46          | ((X3) != (X2))
% 0.19/0.46          | (r1_orders_2 @ X1 @ X5 @ X2)
% 0.19/0.46          | ((X4) != (X5))
% 0.19/0.46          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 0.19/0.46          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X1))
% 0.19/0.46          | ~ (l1_orders_2 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [t60_yellow_0])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X5 : $i]:
% 0.19/0.46         (~ (l1_orders_2 @ X1)
% 0.19/0.46          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X1))
% 0.19/0.46          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X0))
% 0.19/0.46          | (r1_orders_2 @ X1 @ X5 @ X2)
% 0.19/0.46          | ~ (r1_orders_2 @ X0 @ X5 @ X2)
% 0.19/0.46          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.19/0.46          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.19/0.46          | ~ (m1_yellow_0 @ X0 @ X1))),
% 0.19/0.46      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (m1_yellow_0 @ X0 @ sk_B)
% 0.19/0.46          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.19/0.46          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.46          | ~ (r1_orders_2 @ X0 @ sk_D @ X1)
% 0.19/0.46          | (r1_orders_2 @ sk_B @ sk_D @ X1)
% 0.19/0.46          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.46          | ~ (l1_orders_2 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '7'])).
% 0.19/0.46  thf('9', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_l1_waybel_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_struct_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i]:
% 0.19/0.46         (~ (l1_waybel_0 @ X6 @ X7) | (l1_orders_2 @ X6) | ~ (l1_struct_0 @ X7))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.19/0.46  thf('11', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('13', plain, ((l1_orders_2 @ sk_B)),
% 0.19/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (m1_yellow_0 @ X0 @ sk_B)
% 0.19/0.46          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.19/0.46          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.46          | ~ (r1_orders_2 @ X0 @ sk_D @ X1)
% 0.19/0.46          | (r1_orders_2 @ sk_B @ sk_D @ X1)
% 0.19/0.46          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['8', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.46          | (r1_orders_2 @ sk_B @ sk_D @ sk_E)
% 0.19/0.46          | ~ (r1_orders_2 @ X0 @ sk_D @ sk_E)
% 0.19/0.46          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.19/0.46          | ~ (m1_yellow_0 @ X0 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '14'])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      ((~ (m1_yellow_0 @ sk_C @ sk_B)
% 0.19/0.46        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C))
% 0.19/0.46        | ~ (r1_orders_2 @ sk_C @ sk_D @ sk_E)
% 0.19/0.46        | (r1_orders_2 @ sk_B @ sk_D @ sk_E))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '15'])).
% 0.19/0.46  thf('17', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d8_yellow_6, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_struct_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( l1_waybel_0 @ B @ A ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( l1_waybel_0 @ C @ A ) =>
% 0.19/0.46               ( ( m1_yellow_6 @ C @ A @ B ) <=>
% 0.19/0.46                 ( ( m1_yellow_0 @ C @ B ) & 
% 0.19/0.46                   ( ( u1_waybel_0 @ A @ C ) =
% 0.19/0.46                     ( k2_partfun1 @
% 0.19/0.46                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.46                       ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.46         (~ (l1_waybel_0 @ X8 @ X9)
% 0.19/0.46          | ~ (m1_yellow_6 @ X10 @ X9 @ X8)
% 0.19/0.46          | (m1_yellow_0 @ X10 @ X8)
% 0.19/0.46          | ~ (l1_waybel_0 @ X10 @ X9)
% 0.19/0.46          | ~ (l1_struct_0 @ X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.46        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.19/0.46        | (m1_yellow_0 @ sk_C @ sk_B)
% 0.19/0.46        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.46  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('21', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_m1_yellow_6, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.46       ( ![C:$i]: ( ( m1_yellow_6 @ C @ A @ B ) => ( l1_waybel_0 @ C @ A ) ) ) ))).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         (~ (l1_struct_0 @ X11)
% 0.19/0.46          | ~ (l1_waybel_0 @ X12 @ X11)
% 0.19/0.46          | (l1_waybel_0 @ X13 @ X11)
% 0.19/0.46          | ~ (m1_yellow_6 @ X13 @ X11 @ X12))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (((l1_waybel_0 @ sk_C @ sk_A)
% 0.19/0.46        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.19/0.46        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.46  thf('24', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('26', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.46  thf('27', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('28', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.19/0.46      inference('demod', [status(thm)], ['19', '20', '26', '27'])).
% 0.19/0.46  thf('29', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('30', plain, (((sk_E) = (sk_G))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('31', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.46  thf('32', plain, ((r1_orders_2 @ sk_C @ sk_F @ sk_G)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('33', plain, (((sk_D) = (sk_F))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('34', plain, (((sk_E) = (sk_G))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('35', plain, ((r1_orders_2 @ sk_C @ sk_D @ sk_E)),
% 0.19/0.46      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.19/0.46  thf('36', plain, ((r1_orders_2 @ sk_B @ sk_D @ sk_E)),
% 0.19/0.46      inference('demod', [status(thm)], ['16', '28', '31', '35'])).
% 0.19/0.46  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
