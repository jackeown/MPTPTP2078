%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lbIgQ0Pt4G

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 295 expanded)
%              Number of leaves         :   30 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          :  951 (3837 expanded)
%              Number of equality atoms :   27 (  77 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('4',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t8_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( X5 = X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ ( k3_yellow_0 @ X14 ) @ X13 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v1_yellow_0 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('28',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('37',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ X17 @ X15 )
      | ~ ( r1_orders_2 @ X16 @ X18 @ X17 )
      | ~ ( r2_hidden @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('51',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('53',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('59',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ X6 @ X6 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['54'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('64',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('67',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['54'])).

thf('77',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','60','61','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lbIgQ0Pt4G
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:12:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 142 iterations in 0.080s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(t8_waybel_7, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.21/0.54         ( l1_orders_2 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.21/0.54             ( v13_waybel_0 @ B @ A ) & 
% 0.21/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.21/0.54             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.54            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.21/0.54            ( l1_orders_2 @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.21/0.54                ( v13_waybel_0 @ B @ A ) & 
% 0.21/0.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.21/0.54                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.21/0.54        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.21/0.54       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(rc3_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ?[B:$i]:
% 0.21/0.54       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.54  thf(d7_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (((X20) = (X19))
% 0.21/0.54          | (v1_subset_1 @ X20 @ X19)
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain, (![X6 : $i]: ~ (v1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.54  thf('8', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.21/0.54      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.54  thf(t8_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54           ( ( ![D:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.54                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.54             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.54          | ((X5) = (X3))
% 0.21/0.54          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.21/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.21/0.54          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.21/0.54          | ((X1) = (X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r2_hidden @ 
% 0.21/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.54           sk_B_1)
% 0.21/0.54        | (r2_hidden @ 
% 0.21/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.54          | ((X5) = (X3))
% 0.21/0.54          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.21/0.54          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.21/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.21/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.21/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.21/0.54          | ((X1) = (X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (r2_hidden @ 
% 0.21/0.54             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.54             sk_B_1)
% 0.21/0.54        | ~ (r2_hidden @ 
% 0.21/0.54             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.54             (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l3_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.54          | (r2_hidden @ X0 @ X2)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      ((~ (r2_hidden @ 
% 0.21/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.54           sk_B_1)
% 0.21/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['17', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (((r2_hidden @ 
% 0.21/0.54         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['12', '21'])).
% 0.21/0.54  thf('23', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.54  thf(t4_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X9 @ X10)
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.21/0.54          | (m1_subset_1 @ X9 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ 
% 0.21/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.54  thf(t44_yellow_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.21/0.54         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.21/0.54          | (r1_orders_2 @ X14 @ (k3_yellow_0 @ X14) @ X13)
% 0.21/0.54          | ~ (l1_orders_2 @ X14)
% 0.21/0.54          | ~ (v1_yellow_0 @ X14)
% 0.21/0.54          | ~ (v5_orders_2 @ X14)
% 0.21/0.54          | (v2_struct_0 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.54        | ~ (v1_yellow_0 @ sk_A)
% 0.21/0.54        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.54        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.21/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('30', plain, ((v1_yellow_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.21/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.54  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.21/0.54         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.21/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d20_waybel_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_orders_2 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                 ( ![D:$i]:
% 0.21/0.54                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.21/0.54                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.54          | ~ (v13_waybel_0 @ X15 @ X16)
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.54          | (r2_hidden @ X17 @ X15)
% 0.21/0.54          | ~ (r1_orders_2 @ X16 @ X18 @ X17)
% 0.21/0.54          | ~ (r2_hidden @ X18 @ X15)
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.21/0.54          | ~ (l1_orders_2 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (l1_orders_2 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.21/0.54          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.54          | (r2_hidden @ X1 @ sk_B_1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.36/0.54          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.36/0.54          | (r2_hidden @ X1 @ sk_B_1)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54           | (r2_hidden @ X0 @ sk_B_1)
% 0.36/0.54           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.36/0.54           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.36/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['39', '45'])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.36/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54           | (r2_hidden @ X0 @ sk_B_1)
% 0.36/0.54           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.36/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.36/0.54         | (r2_hidden @ 
% 0.36/0.54            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.54            sk_B_1)
% 0.36/0.54         | ~ (m1_subset_1 @ 
% 0.36/0.54              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.54              (u1_struct_0 @ sk_A))))
% 0.36/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '48'])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      ((~ (r2_hidden @ 
% 0.36/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.54           sk_B_1)
% 0.36/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('clc', [status(thm)], ['17', '20'])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (((~ (m1_subset_1 @ 
% 0.36/0.54            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.54            (u1_struct_0 @ sk_A))
% 0.36/0.54         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.36/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.54      inference('clc', [status(thm)], ['49', '50'])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.36/0.54        | (m1_subset_1 @ 
% 0.36/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.54           (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.36/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.54      inference('clc', [status(thm)], ['51', '52'])).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.36/0.54        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('split', [status(esa)], ['54'])).
% 0.36/0.54  thf('56', plain,
% 0.36/0.54      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.36/0.54         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.36/0.54             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['53', '55'])).
% 0.36/0.54  thf('57', plain, (![X6 : $i]: ~ (v1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.36/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.36/0.54  thf('58', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.36/0.54      inference('clc', [status(thm)], ['6', '7'])).
% 0.36/0.54  thf('59', plain, (![X6 : $i]: ~ (v1_subset_1 @ X6 @ X6)),
% 0.36/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.36/0.54       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['56', '59'])).
% 0.36/0.54  thf('61', plain,
% 0.36/0.54      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.36/0.54       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('split', [status(esa)], ['54'])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i]:
% 0.36/0.54         (((X20) = (X19))
% 0.36/0.54          | (v1_subset_1 @ X20 @ X19)
% 0.36/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.36/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.36/0.54  thf(dt_k3_yellow_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_orders_2 @ A ) =>
% 0.36/0.54       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.36/0.54  thf('67', plain,
% 0.36/0.54      (![X12 : $i]:
% 0.36/0.54         ((m1_subset_1 @ (k3_yellow_0 @ X12) @ (u1_struct_0 @ X12))
% 0.36/0.54          | ~ (l1_orders_2 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.36/0.54  thf(t2_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.54  thf('68', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i]:
% 0.36/0.54         ((r2_hidden @ X7 @ X8)
% 0.36/0.54          | (v1_xboole_0 @ X8)
% 0.36/0.54          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.54  thf('69', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (l1_orders_2 @ X0)
% 0.36/0.54          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.36/0.54          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.54  thf('70', plain,
% 0.36/0.54      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.36/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54         | ~ (l1_orders_2 @ sk_A)))
% 0.36/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup+', [status(thm)], ['66', '69'])).
% 0.36/0.54  thf('71', plain,
% 0.36/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.36/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.36/0.54  thf('72', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('73', plain,
% 0.36/0.54      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 0.36/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.36/0.54  thf('74', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('75', plain,
% 0.36/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.36/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('clc', [status(thm)], ['73', '74'])).
% 0.36/0.54  thf('76', plain,
% 0.36/0.54      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.36/0.54         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.54      inference('split', [status(esa)], ['54'])).
% 0.36/0.54  thf('77', plain,
% 0.36/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.36/0.54       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.54  thf('78', plain, ($false),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['1', '60', '61', '77'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
