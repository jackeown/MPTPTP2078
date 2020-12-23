%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OyYlcdTBkA

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 285 expanded)
%              Number of leaves         :   33 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  581 (5077 expanded)
%              Number of equality atoms :    9 ( 214 expanded)
%              Maximal formula depth    :   22 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( u1_orders_2 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D @ X0 ) @ ( u1_orders_2 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X24 @ X23 )
      | ( l1_waybel_0 @ X25 @ X23 )
      | ~ ( m1_yellow_6 @ X25 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('10',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( l1_orders_2 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('15',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D @ X0 ) @ ( u1_orders_2 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['7','17'])).

thf('19',plain,
    ( ~ ( r1_orders_2 @ sk_C @ sk_D @ sk_E )
    | ( r2_hidden @ ( k4_tarski @ sk_D @ sk_E ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf('20',plain,(
    r1_orders_2 @ sk_C @ sk_F @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_orders_2 @ sk_C @ sk_D @ sk_E ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    r2_hidden @ ( k4_tarski @ sk_D @ sk_E ) @ ( u1_orders_2 @ sk_C ) ),
    inference(demod,[status(thm)],['19','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( m1_yellow_6 @ X22 @ X21 @ X20 )
      | ( m1_yellow_0 @ X22 @ X20 )
      | ~ ( l1_waybel_0 @ X22 @ X21 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('27',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('30',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( m1_yellow_0 @ X14 @ X15 )
      | ( r1_tarski @ ( u1_orders_2 @ X14 ) @ ( u1_orders_2 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('33',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( l1_orders_2 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('36',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('40',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_B ) ),
    inference(demod,[status(thm)],['33','38','39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_orders_2 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ ( k4_tarski @ sk_D @ sk_E ) @ ( u1_orders_2 @ sk_C ) ),
    inference(demod,[status(thm)],['19','23'])).

thf('46',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_orders_2 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_tarski @ sk_D @ sk_E ) @ ( u1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_B ) )
    | ( r2_hidden @ ( k4_tarski @ sk_D @ sk_E ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( u1_orders_2 @ X12 ) )
      | ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_orders_2 @ sk_B @ sk_D @ sk_E )
    | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_B ) )
    | ( r1_orders_2 @ sk_B @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ~ ( r1_orders_2 @ sk_B @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ ( u1_orders_2 @ sk_B ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','59'])).

thf('61',plain,(
    $false ),
    inference('sup-',[status(thm)],['24','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OyYlcdTBkA
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 62 iterations in 0.026s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(t20_yellow_6, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                       ( ![F:$i]:
% 0.21/0.49                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                           ( ![G:$i]:
% 0.21/0.49                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                               ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.21/0.49                                   ( r1_orders_2 @ C @ F @ G ) ) =>
% 0.21/0.49                                 ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_struct_0 @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                      ( ![E:$i]:
% 0.21/0.49                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                          ( ![F:$i]:
% 0.21/0.49                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                              ( ![G:$i]:
% 0.21/0.49                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                                  ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.21/0.49                                      ( r1_orders_2 @ C @ F @ G ) ) =>
% 0.21/0.49                                    ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t20_yellow_6])).
% 0.21/0.49  thf('0', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, (((sk_E) = (sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain, (((sk_D) = (sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(d9_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.21/0.49                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.49          | ~ (r1_orders_2 @ X12 @ X11 @ X13)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X11 @ X13) @ (u1_orders_2 @ X12))
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.49          | ~ (l1_orders_2 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ sk_C)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ sk_D @ X0) @ (u1_orders_2 @ sk_C))
% 0.21/0.49          | ~ (r1_orders_2 @ sk_C @ sk_D @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m1_yellow_6, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49       ( ![C:$i]: ( ( m1_yellow_6 @ C @ A @ B ) => ( l1_waybel_0 @ C @ A ) ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X23)
% 0.21/0.49          | ~ (l1_waybel_0 @ X24 @ X23)
% 0.21/0.49          | (l1_waybel_0 @ X25 @ X23)
% 0.21/0.49          | ~ (m1_yellow_6 @ X25 @ X23 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((l1_waybel_0 @ sk_C @ sk_A)
% 0.21/0.49        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.49  thf(dt_l1_waybel_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.49          | (l1_orders_2 @ X18)
% 0.21/0.49          | ~ (l1_struct_0 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.49  thf('15', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ((l1_orders_2 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ sk_D @ X0) @ (u1_orders_2 @ sk_C))
% 0.21/0.49          | ~ (r1_orders_2 @ sk_C @ sk_D @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((~ (r1_orders_2 @ sk_C @ sk_D @ sk_E)
% 0.21/0.49        | (r2_hidden @ (k4_tarski @ sk_D @ sk_E) @ (u1_orders_2 @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '18'])).
% 0.21/0.49  thf('20', plain, ((r1_orders_2 @ sk_C @ sk_F @ sk_G)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, (((sk_D) = (sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain, (((sk_E) = (sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain, ((r1_orders_2 @ sk_C @ sk_D @ sk_E)),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((r2_hidden @ (k4_tarski @ sk_D @ sk_E) @ (u1_orders_2 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '23'])).
% 0.21/0.49  thf('25', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d8_yellow_6, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( l1_waybel_0 @ C @ A ) =>
% 0.21/0.49               ( ( m1_yellow_6 @ C @ A @ B ) <=>
% 0.21/0.49                 ( ( m1_yellow_0 @ C @ B ) & 
% 0.21/0.49                   ( ( u1_waybel_0 @ A @ C ) =
% 0.21/0.49                     ( k2_partfun1 @
% 0.21/0.49                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.49                       ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.49         (~ (l1_waybel_0 @ X20 @ X21)
% 0.21/0.49          | ~ (m1_yellow_6 @ X22 @ X21 @ X20)
% 0.21/0.49          | (m1_yellow_0 @ X22 @ X20)
% 0.21/0.49          | ~ (l1_waybel_0 @ X22 @ X21)
% 0.21/0.49          | ~ (l1_struct_0 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.21/0.49        | (m1_yellow_0 @ sk_C @ sk_B)
% 0.21/0.49        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.49  thf('30', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.49  thf(d13_yellow_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_orders_2 @ B ) =>
% 0.21/0.49           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.21/0.49             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ X14)
% 0.21/0.49          | ~ (m1_yellow_0 @ X14 @ X15)
% 0.21/0.49          | (r1_tarski @ (u1_orders_2 @ X14) @ (u1_orders_2 @ X15))
% 0.21/0.49          | ~ (l1_orders_2 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((~ (l1_orders_2 @ sk_B)
% 0.21/0.49        | (r1_tarski @ (u1_orders_2 @ sk_C) @ (u1_orders_2 @ sk_B))
% 0.21/0.49        | ~ (l1_orders_2 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.49          | (l1_orders_2 @ X18)
% 0.21/0.49          | ~ (l1_struct_0 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.49  thf('36', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((l1_orders_2 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('40', plain, ((r1_tarski @ (u1_orders_2 @ sk_C) @ (u1_orders_2 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '38', '39'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X2 : $i, X4 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_orders_2 @ sk_C) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_orders_2 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf(t5_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.49          | ~ (v1_xboole_0 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_orders_2 @ sk_B))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (u1_orders_2 @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      ((r2_hidden @ (k4_tarski @ sk_D @ sk_E) @ (u1_orders_2 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '23'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_orders_2 @ sk_C) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_orders_2 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf(t4_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.49          | (m1_subset_1 @ X5 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X0 @ (u1_orders_2 @ sk_B))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (u1_orders_2 @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      ((m1_subset_1 @ (k4_tarski @ sk_D @ sk_E) @ (u1_orders_2 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '48'])).
% 0.21/0.49  thf(t2_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X0 @ X1)
% 0.21/0.49          | (v1_xboole_0 @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_orders_2 @ sk_B))
% 0.21/0.49        | (r2_hidden @ (k4_tarski @ sk_D @ sk_E) @ (u1_orders_2 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (u1_orders_2 @ X12))
% 0.21/0.49          | (r1_orders_2 @ X12 @ X11 @ X13)
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.49          | ~ (l1_orders_2 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_orders_2 @ sk_B))
% 0.21/0.49        | ~ (l1_orders_2 @ sk_B)
% 0.21/0.49        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.49        | (r1_orders_2 @ sk_B @ sk_D @ sk_E)
% 0.21/0.49        | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('54', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('55', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('56', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_orders_2 @ sk_B))
% 0.21/0.49        | (r1_orders_2 @ sk_B @ sk_D @ sk_E))),
% 0.21/0.49      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.21/0.49  thf('58', plain, (~ (r1_orders_2 @ sk_B @ sk_D @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain, ((v1_xboole_0 @ (u1_orders_2 @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.49  thf('60', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_orders_2 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '59'])).
% 0.21/0.49  thf('61', plain, ($false), inference('sup-', [status(thm)], ['24', '60'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
