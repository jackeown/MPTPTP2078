%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0n2kKKuUB5

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:55 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 175 expanded)
%              Number of leaves         :   35 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  580 (2841 expanded)
%              Number of equality atoms :   13 ( 121 expanded)
%              Maximal formula depth    :   22 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r1_orders_2 @ sk_B @ sk_D_2 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( m1_yellow_6 @ X25 @ X24 @ X23 )
      | ( m1_yellow_0 @ X25 @ X23 )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('3',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ( m1_yellow_0 @ sk_C_1 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_yellow_6 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_waybel_0 @ X27 @ X26 )
      | ( l1_waybel_0 @ X28 @ X26 )
      | ~ ( m1_yellow_6 @ X28 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('7',plain,
    ( ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_yellow_0 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['3','4','10','11'])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_yellow_0 @ X17 @ X18 )
      | ( r1_tarski @ ( u1_orders_2 @ X17 ) @ ( u1_orders_2 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('14',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( l1_orders_2 @ X21 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('17',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( l1_orders_2 @ X21 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('22',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_B ) ),
    inference(demod,[status(thm)],['14','19','24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_orders_2 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_orders_2 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_orders_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    r2_hidden @ ( u1_orders_2 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_orders_2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_D_2 = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( u1_orders_2 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X0 ) @ ( u1_orders_2 @ sk_C_1 ) )
      | ~ ( r1_orders_2 @ sk_C_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X0 ) @ ( u1_orders_2 @ sk_C_1 ) )
      | ~ ( r1_orders_2 @ sk_C_1 @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_orders_2 @ sk_C_1 @ sk_D_2 @ sk_E )
    | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( u1_orders_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    r1_orders_2 @ sk_C_1 @ sk_F @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_D_2 = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_E = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_orders_2 @ sk_C_1 @ sk_D_2 @ sk_E ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( u1_orders_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','46'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k3_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_orders_2 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_orders_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','50'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('52',plain,(
    ! [X7: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('53',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( u1_orders_2 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( u1_orders_2 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('55',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_orders_2 @ sk_B @ sk_D_2 @ sk_E )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_orders_2 @ sk_B @ sk_D_2 @ sk_E ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0n2kKKuUB5
% 0.13/0.37  % Computer   : n004.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:45:24 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 145 iterations in 0.098s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.23/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.23/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.54  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.23/0.54  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.23/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.23/0.54  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.23/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.54  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.23/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.23/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.23/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(t20_yellow_6, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_struct_0 @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( l1_waybel_0 @ B @ A ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.23/0.54               ( ![D:$i]:
% 0.23/0.54                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.23/0.54                   ( ![E:$i]:
% 0.23/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.23/0.54                       ( ![F:$i]:
% 0.23/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.23/0.54                           ( ![G:$i]:
% 0.23/0.54                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.23/0.54                               ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.23/0.54                                   ( r1_orders_2 @ C @ F @ G ) ) =>
% 0.23/0.54                                 ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ( l1_struct_0 @ A ) =>
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ( l1_waybel_0 @ B @ A ) =>
% 0.23/0.54              ( ![C:$i]:
% 0.23/0.54                ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.23/0.54                  ( ![D:$i]:
% 0.23/0.54                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.23/0.54                      ( ![E:$i]:
% 0.23/0.54                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.23/0.54                          ( ![F:$i]:
% 0.23/0.54                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.23/0.54                              ( ![G:$i]:
% 0.23/0.54                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.23/0.54                                  ( ( ( ( D ) = ( F ) ) & ( ( E ) = ( G ) ) & 
% 0.23/0.54                                      ( r1_orders_2 @ C @ F @ G ) ) =>
% 0.23/0.54                                    ( r1_orders_2 @ B @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t20_yellow_6])).
% 0.23/0.54  thf('0', plain, (~ (r1_orders_2 @ sk_B @ sk_D_2 @ sk_E)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('1', plain, ((m1_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d8_yellow_6, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_struct_0 @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( l1_waybel_0 @ B @ A ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( l1_waybel_0 @ C @ A ) =>
% 0.23/0.54               ( ( m1_yellow_6 @ C @ A @ B ) <=>
% 0.23/0.54                 ( ( m1_yellow_0 @ C @ B ) & 
% 0.23/0.54                   ( ( u1_waybel_0 @ A @ C ) =
% 0.23/0.54                     ( k2_partfun1 @
% 0.23/0.54                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.23/0.54                       ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.54         (~ (l1_waybel_0 @ X23 @ X24)
% 0.23/0.54          | ~ (m1_yellow_6 @ X25 @ X24 @ X23)
% 0.23/0.54          | (m1_yellow_0 @ X25 @ X23)
% 0.23/0.54          | ~ (l1_waybel_0 @ X25 @ X24)
% 0.23/0.54          | ~ (l1_struct_0 @ X24))),
% 0.23/0.54      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      ((~ (l1_struct_0 @ sk_A)
% 0.23/0.54        | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.23/0.54        | (m1_yellow_0 @ sk_C_1 @ sk_B)
% 0.23/0.54        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.54  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('5', plain, ((m1_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(dt_m1_yellow_6, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.23/0.54       ( ![C:$i]: ( ( m1_yellow_6 @ C @ A @ B ) => ( l1_waybel_0 @ C @ A ) ) ) ))).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.23/0.54         (~ (l1_struct_0 @ X26)
% 0.23/0.54          | ~ (l1_waybel_0 @ X27 @ X26)
% 0.23/0.54          | (l1_waybel_0 @ X28 @ X26)
% 0.23/0.54          | ~ (m1_yellow_6 @ X28 @ X26 @ X27))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      (((l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.23/0.54        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.23/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf('8', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('10', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.23/0.54      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.23/0.54  thf('11', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('12', plain, ((m1_yellow_0 @ sk_C_1 @ sk_B)),
% 0.23/0.54      inference('demod', [status(thm)], ['3', '4', '10', '11'])).
% 0.23/0.54  thf(d13_yellow_0, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_orders_2 @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( l1_orders_2 @ B ) =>
% 0.23/0.54           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.23/0.54             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.23/0.54               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X17 : $i, X18 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ X17)
% 0.23/0.54          | ~ (m1_yellow_0 @ X17 @ X18)
% 0.23/0.54          | (r1_tarski @ (u1_orders_2 @ X17) @ (u1_orders_2 @ X18))
% 0.23/0.54          | ~ (l1_orders_2 @ X18))),
% 0.23/0.54      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      ((~ (l1_orders_2 @ sk_B)
% 0.23/0.54        | (r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_B))
% 0.23/0.54        | ~ (l1_orders_2 @ sk_C_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.54  thf('15', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(dt_l1_waybel_0, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_struct_0 @ A ) =>
% 0.23/0.54       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X21 : $i, X22 : $i]:
% 0.23/0.54         (~ (l1_waybel_0 @ X21 @ X22)
% 0.23/0.54          | (l1_orders_2 @ X21)
% 0.23/0.54          | ~ (l1_struct_0 @ X22))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.23/0.54  thf('17', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('19', plain, ((l1_orders_2 @ sk_B)),
% 0.23/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.23/0.54  thf('20', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.23/0.54      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      (![X21 : $i, X22 : $i]:
% 0.23/0.54         (~ (l1_waybel_0 @ X21 @ X22)
% 0.23/0.54          | (l1_orders_2 @ X21)
% 0.23/0.54          | ~ (l1_struct_0 @ X22))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.23/0.54  thf('22', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.54  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('24', plain, ((l1_orders_2 @ sk_C_1)),
% 0.23/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      ((r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['14', '19', '24'])).
% 0.23/0.54  thf(t3_subset, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      (![X11 : $i, X13 : $i]:
% 0.23/0.54         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      ((m1_subset_1 @ (u1_orders_2 @ sk_C_1) @ 
% 0.23/0.54        (k1_zfmisc_1 @ (u1_orders_2 @ sk_B)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.54  thf(t2_subset, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      (![X9 : $i, X10 : $i]:
% 0.23/0.54         ((r2_hidden @ X9 @ X10)
% 0.23/0.54          | (v1_xboole_0 @ X10)
% 0.23/0.54          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.23/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_orders_2 @ sk_B)))
% 0.23/0.54        | (r2_hidden @ (u1_orders_2 @ sk_C_1) @ 
% 0.23/0.54           (k1_zfmisc_1 @ (u1_orders_2 @ sk_B))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.54  thf(fc1_subset_1, axiom,
% 0.23/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.54  thf('30', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.23/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      ((r2_hidden @ (u1_orders_2 @ sk_C_1) @ 
% 0.23/0.54        (k1_zfmisc_1 @ (u1_orders_2 @ sk_B)))),
% 0.23/0.54      inference('clc', [status(thm)], ['29', '30'])).
% 0.23/0.54  thf('32', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('33', plain, (((sk_E) = (sk_G))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('34', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_C_1))),
% 0.23/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.54  thf('35', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('36', plain, (((sk_D_2) = (sk_F))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('37', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_C_1))),
% 0.23/0.54      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.54  thf(d9_orders_2, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_orders_2 @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.23/0.54                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('38', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.23/0.54          | ~ (r1_orders_2 @ X15 @ X14 @ X16)
% 0.23/0.54          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ (u1_orders_2 @ X15))
% 0.23/0.54          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.23/0.54          | ~ (l1_orders_2 @ X15))),
% 0.23/0.54      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.23/0.54  thf('39', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ sk_C_1)
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.23/0.54          | (r2_hidden @ (k4_tarski @ sk_D_2 @ X0) @ (u1_orders_2 @ sk_C_1))
% 0.23/0.54          | ~ (r1_orders_2 @ sk_C_1 @ sk_D_2 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.23/0.54  thf('40', plain, ((l1_orders_2 @ sk_C_1)),
% 0.23/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('41', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.23/0.54          | (r2_hidden @ (k4_tarski @ sk_D_2 @ X0) @ (u1_orders_2 @ sk_C_1))
% 0.23/0.54          | ~ (r1_orders_2 @ sk_C_1 @ sk_D_2 @ X0))),
% 0.23/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.23/0.54  thf('42', plain,
% 0.23/0.54      ((~ (r1_orders_2 @ sk_C_1 @ sk_D_2 @ sk_E)
% 0.23/0.54        | (r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ (u1_orders_2 @ sk_C_1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['34', '41'])).
% 0.23/0.54  thf('43', plain, ((r1_orders_2 @ sk_C_1 @ sk_F @ sk_G)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('44', plain, (((sk_D_2) = (sk_F))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('45', plain, (((sk_E) = (sk_G))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('46', plain, ((r1_orders_2 @ sk_C_1 @ sk_D_2 @ sk_E)),
% 0.23/0.54      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.23/0.54  thf('47', plain,
% 0.23/0.54      ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ (u1_orders_2 @ sk_C_1))),
% 0.23/0.54      inference('demod', [status(thm)], ['42', '46'])).
% 0.23/0.54  thf(d4_tarski, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.23/0.54       ( ![C:$i]:
% 0.23/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.23/0.54           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.23/0.54  thf('48', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.54          | ~ (r2_hidden @ X2 @ X0)
% 0.23/0.54          | (r2_hidden @ X2 @ X3)
% 0.23/0.54          | ((X3) != (k3_tarski @ X1)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_tarski])).
% 0.23/0.54  thf('49', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         ((r2_hidden @ X2 @ (k3_tarski @ X1))
% 0.23/0.54          | ~ (r2_hidden @ X2 @ X0)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.23/0.54  thf('50', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r2_hidden @ (u1_orders_2 @ sk_C_1) @ X0)
% 0.23/0.54          | (r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ (k3_tarski @ X0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['47', '49'])).
% 0.23/0.54  thf('51', plain,
% 0.23/0.54      ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ 
% 0.23/0.54        (k3_tarski @ (k1_zfmisc_1 @ (u1_orders_2 @ sk_B))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['31', '50'])).
% 0.23/0.54  thf(t99_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.23/0.54  thf('52', plain, (![X7 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X7)) = (X7))),
% 0.23/0.54      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.23/0.54  thf('53', plain,
% 0.23/0.54      ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ (u1_orders_2 @ sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.23/0.54  thf('54', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.23/0.54          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (u1_orders_2 @ X15))
% 0.23/0.54          | (r1_orders_2 @ X15 @ X14 @ X16)
% 0.23/0.54          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.23/0.54          | ~ (l1_orders_2 @ X15))),
% 0.23/0.54      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.23/0.54  thf('55', plain,
% 0.23/0.54      ((~ (l1_orders_2 @ sk_B)
% 0.23/0.54        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.23/0.54        | (r1_orders_2 @ sk_B @ sk_D_2 @ sk_E)
% 0.23/0.54        | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_B)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.23/0.54  thf('56', plain, ((l1_orders_2 @ sk_B)),
% 0.23/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.23/0.54  thf('57', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('58', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_B))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('59', plain, ((r1_orders_2 @ sk_B @ sk_D_2 @ sk_E)),
% 0.23/0.54      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.23/0.54  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
