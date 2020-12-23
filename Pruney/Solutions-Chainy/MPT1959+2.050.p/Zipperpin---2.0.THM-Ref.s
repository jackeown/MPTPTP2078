%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RPG08Wi5y1

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 164 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :   19
%              Number of atoms          :  884 (2486 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t8_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
            <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_7])).

thf('0',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('4',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t39_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( ( k1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B )
            & ( ( k2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( ( k1_yellow_0 @ X9 @ ( k6_domain_1 @ ( u1_struct_0 @ X9 ) @ X8 ) )
        = X8 )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_0])).

thf('6',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ ( k3_yellow_0 @ X11 ) @ X10 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v1_yellow_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d20_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r1_orders_2 @ X13 @ X15 @ X14 )
      | ~ ( r2_hidden @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('42',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('50',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ( v1_subset_1 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ X2 @ X2 ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ( v1_subset_1 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('60',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('64',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('68',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('72',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RPG08Wi5y1
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 139 iterations in 0.074s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.20/0.53  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.53  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.20/0.53  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(t8_waybel_7, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.20/0.53         ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.20/0.53             ( v13_waybel_0 @ B @ A ) & 
% 0.20/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.20/0.53             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.20/0.53            ( l1_orders_2 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.20/0.53                ( v13_waybel_0 @ B @ A ) & 
% 0.20/0.53                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.20/0.53                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.20/0.53        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.20/0.53       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t49_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.53         ( ( A ) = ( B ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.20/0.53          | ((X1) = (X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.20/0.53        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t39_yellow_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ( ( k1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.20/0.53               ( B ) ) & 
% 0.20/0.53             ( ( k2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.20/0.53               ( B ) ) ) ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.53          | ((k1_yellow_0 @ X9 @ (k6_domain_1 @ (u1_struct_0 @ X9) @ X8))
% 0.20/0.53              = (X8))
% 0.20/0.53          | ~ (l1_orders_2 @ X9)
% 0.20/0.53          | ~ (v5_orders_2 @ X9)
% 0.20/0.53          | ~ (v3_orders_2 @ X9)
% 0.20/0.53          | (v2_struct_0 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_yellow_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53        | ((k1_yellow_0 @ sk_A @ 
% 0.20/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53            = (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k1_yellow_0 @ sk_A @ 
% 0.20/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53            = (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.53  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((((k1_yellow_0 @ sk_A @ 
% 0.20/0.53          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53          = (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.20/0.53      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf(dt_k1_yellow_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( l1_orders_2 @ A ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (l1_orders_2 @ X5)
% 0.20/0.53          | (m1_subset_1 @ (k1_yellow_0 @ X5 @ X6) @ (u1_struct_0 @ X5)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (l1_orders_2 @ X5)
% 0.20/0.53          | (m1_subset_1 @ (k1_yellow_0 @ X5 @ X6) @ (u1_struct_0 @ X5)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.20/0.53  thf(t44_yellow_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.20/0.53         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.53          | (r1_orders_2 @ X11 @ (k3_yellow_0 @ X11) @ X10)
% 0.20/0.53          | ~ (l1_orders_2 @ X11)
% 0.20/0.53          | ~ (v1_yellow_0 @ X11)
% 0.20/0.53          | ~ (v5_orders_2 @ X11)
% 0.20/0.53          | (v2_struct_0 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (l1_orders_2 @ X0)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v5_orders_2 @ X0)
% 0.20/0.53          | ~ (v1_yellow_0 @ X0)
% 0.20/0.53          | ~ (l1_orders_2 @ X0)
% 0.20/0.53          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.20/0.53          | ~ (v1_yellow_0 @ X0)
% 0.20/0.53          | ~ (v5_orders_2 @ X0)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (l1_orders_2 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(dt_k3_yellow_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_orders_2 @ A ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X7 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k3_yellow_0 @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.53          | ~ (l1_orders_2 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d20_waybel_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_orders_2 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.20/0.53             ( ![C:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                 ( ![D:$i]:
% 0.20/0.53                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.20/0.53                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.53          | ~ (v13_waybel_0 @ X12 @ X13)
% 0.20/0.53          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.53          | (r2_hidden @ X14 @ X12)
% 0.20/0.53          | ~ (r1_orders_2 @ X13 @ X15 @ X14)
% 0.20/0.53          | ~ (r2_hidden @ X15 @ X12)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.20/0.53          | ~ (l1_orders_2 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X1 @ sk_B_1)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X1 @ sk_B_1)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.20/0.53          | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '25'])).
% 0.20/0.53  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.20/0.53          | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.20/0.53           | (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (l1_orders_2 @ sk_A)
% 0.20/0.53           | (v2_struct_0 @ sk_A)
% 0.20/0.53           | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53           | ~ (v1_yellow_0 @ sk_A)
% 0.20/0.53           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.20/0.53           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '29'])).
% 0.20/0.53  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain, ((v1_yellow_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.20/0.53           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.20/0.53  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.20/0.53           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (l1_orders_2 @ sk_A)
% 0.20/0.53           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '36'])).
% 0.20/0.53  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.20/0.53         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['12', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.20/0.53          | ((X1) = (X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.20/0.53         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (((((u1_struct_0 @ sk_A) = (sk_B_1)) | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 0.20/0.53         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.20/0.53        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.20/0.53         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.20/0.53             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['45', '47'])).
% 0.20/0.53  thf(rc3_subset_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ?[B:$i]:
% 0.20/0.53       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.53  thf('49', plain, (![X2 : $i]: ~ (v1_subset_1 @ (sk_B @ X2) @ X2)),
% 0.20/0.53      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X2 : $i]: (m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.20/0.53  thf(d7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (((X17) = (X16))
% 0.20/0.53          | (v1_subset_1 @ X17 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain, (![X2 : $i]: ~ (v1_subset_1 @ (sk_B @ X2) @ X2)),
% 0.20/0.53      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.20/0.53  thf('54', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.53  thf('55', plain, (![X2 : $i]: ~ (v1_subset_1 @ X2 @ X2)),
% 0.20/0.53      inference('demod', [status(thm)], ['49', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.20/0.53       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.20/0.53       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['46'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (((X17) = (X16))
% 0.20/0.53          | (v1_subset_1 @ X17 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X7 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k3_yellow_0 @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.53          | ~ (l1_orders_2 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1) | ~ (l1_orders_2 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.20/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf(t2_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         ((r2_hidden @ X3 @ X4)
% 0.20/0.53          | (v1_xboole_0 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.20/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.20/0.53         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.20/0.53         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['46'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.20/0.53       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.53  thf('73', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '72'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
