%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tv1jpM5rqC

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 204 expanded)
%              Number of leaves         :   33 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  907 (2809 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
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
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( r1_orders_2 @ X19 @ ( k3_yellow_0 @ X19 ) @ X18 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v1_yellow_0 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('14',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( r1_orders_2 @ X21 @ X23 @ X22 )
      | ~ ( r2_hidden @ X23 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','44'])).

thf('46',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('47',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('53',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ X6 @ X6 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('58',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X15: $i] :
      ( ( ( k3_yellow_0 @ X15 )
        = ( k1_yellow_0 @ X15 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','66'])).

thf('68',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['48'])).

thf('74',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','54','55','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tv1jpM5rqC
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 196 iterations in 0.092s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.54  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.19/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.54  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.19/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.54  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.19/0.54  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.19/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.54  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.19/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.54  thf(t8_waybel_7, conjecture,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.19/0.54         ( l1_orders_2 @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.19/0.54             ( v13_waybel_0 @ B @ A ) & 
% 0.19/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.54           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.19/0.54             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i]:
% 0.19/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.54            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.19/0.54            ( l1_orders_2 @ A ) ) =>
% 0.19/0.54          ( ![B:$i]:
% 0.19/0.54            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.19/0.54                ( v13_waybel_0 @ B @ A ) & 
% 0.19/0.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.54              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.19/0.54                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.19/0.54        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.19/0.54       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(rc3_subset_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ?[B:$i]:
% 0.19/0.54       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.19/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.19/0.54  thf('3', plain,
% 0.19/0.54      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.19/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.19/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.19/0.54  thf(d7_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (![X24 : $i, X25 : $i]:
% 0.19/0.54         (((X25) = (X24))
% 0.19/0.54          | (v1_subset_1 @ X25 @ X24)
% 0.19/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.54  thf('7', plain, (![X6 : $i]: ~ (v1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.19/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.19/0.54  thf('8', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.19/0.54      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.54  thf('9', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.19/0.54      inference('demod', [status(thm)], ['3', '8'])).
% 0.19/0.54  thf(t8_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( ![C:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54           ( ( ![D:$i]:
% 0.19/0.54               ( ( m1_subset_1 @ D @ A ) =>
% 0.19/0.54                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.19/0.54             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.19/0.54          | ((X5) = (X3))
% 0.19/0.54          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 0.19/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.19/0.54  thf('11', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.19/0.54          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.19/0.54          | ((X1) = (X0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.54  thf('12', plain,
% 0.19/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.54        | (m1_subset_1 @ 
% 0.19/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.19/0.54           (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['2', '11'])).
% 0.19/0.54  thf(t44_yellow_0, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.19/0.54         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      (![X18 : $i, X19 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.19/0.54          | (r1_orders_2 @ X19 @ (k3_yellow_0 @ X19) @ X18)
% 0.19/0.54          | ~ (l1_orders_2 @ X19)
% 0.19/0.54          | ~ (v1_yellow_0 @ X19)
% 0.19/0.54          | ~ (v5_orders_2 @ X19)
% 0.19/0.54          | (v2_struct_0 @ X19))),
% 0.19/0.54      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.54        | (v2_struct_0 @ sk_A)
% 0.19/0.54        | ~ (v5_orders_2 @ sk_A)
% 0.19/0.54        | ~ (v1_yellow_0 @ sk_A)
% 0.19/0.54        | ~ (l1_orders_2 @ sk_A)
% 0.19/0.54        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.19/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.54  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('16', plain, ((v1_yellow_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.54        | (v2_struct_0 @ sk_A)
% 0.19/0.54        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.19/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.19/0.54  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.19/0.54         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('clc', [status(thm)], ['18', '19'])).
% 0.19/0.54  thf('21', plain,
% 0.19/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.19/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t4_subset, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.19/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X9 @ X10)
% 0.19/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.19/0.54          | (m1_subset_1 @ X9 @ X11))),
% 0.19/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.19/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['21', '24'])).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(d20_waybel_0, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_orders_2 @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.19/0.54             ( ![C:$i]:
% 0.19/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54                 ( ![D:$i]:
% 0.19/0.54                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.19/0.54                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf('27', plain,
% 0.19/0.54      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.54          | ~ (v13_waybel_0 @ X20 @ X21)
% 0.19/0.54          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.19/0.54          | (r2_hidden @ X22 @ X20)
% 0.19/0.54          | ~ (r1_orders_2 @ X21 @ X23 @ X22)
% 0.19/0.54          | ~ (r2_hidden @ X23 @ X20)
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.19/0.54          | ~ (l1_orders_2 @ X21))),
% 0.19/0.54      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.19/0.54  thf('28', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (l1_orders_2 @ sk_A)
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.19/0.54          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.19/0.54          | (r2_hidden @ X1 @ sk_B_1)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.54  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('30', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.19/0.54          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.19/0.54          | (r2_hidden @ X1 @ sk_B_1)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.54           | (r2_hidden @ X0 @ sk_B_1)
% 0.19/0.54           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.19/0.54           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.19/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['25', '31'])).
% 0.19/0.54  thf('33', plain,
% 0.19/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.19/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('34', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.54           | (r2_hidden @ X0 @ sk_B_1)
% 0.19/0.54           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.19/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.54  thf('35', plain,
% 0.19/0.54      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.54         | (r2_hidden @ 
% 0.19/0.54            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.19/0.54            sk_B_1)
% 0.19/0.54         | ~ (m1_subset_1 @ 
% 0.19/0.54              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.19/0.54              (u1_struct_0 @ sk_A))))
% 0.19/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['20', '34'])).
% 0.19/0.54  thf('36', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('37', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.19/0.54      inference('demod', [status(thm)], ['3', '8'])).
% 0.19/0.54  thf('38', plain,
% 0.19/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.19/0.54          | ((X5) = (X3))
% 0.19/0.54          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.19/0.54          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.19/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.19/0.54  thf('39', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.19/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.19/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.19/0.54          | ((X1) = (X0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.54  thf('40', plain,
% 0.19/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.54        | ~ (r2_hidden @ 
% 0.19/0.54             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.19/0.54             sk_B_1)
% 0.19/0.54        | ~ (r2_hidden @ 
% 0.19/0.54             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.19/0.54             (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['36', '39'])).
% 0.19/0.54  thf('41', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(l3_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.54  thf('42', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.54          | (r2_hidden @ X0 @ X2)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.54  thf('43', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.54  thf('44', plain,
% 0.19/0.54      ((~ (r2_hidden @ 
% 0.19/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.19/0.54           sk_B_1)
% 0.19/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('clc', [status(thm)], ['40', '43'])).
% 0.19/0.54  thf('45', plain,
% 0.19/0.54      (((~ (m1_subset_1 @ 
% 0.19/0.54            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.19/0.54            (u1_struct_0 @ sk_A))
% 0.19/0.54         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.19/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('clc', [status(thm)], ['35', '44'])).
% 0.19/0.54  thf('46', plain,
% 0.19/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.54        | (m1_subset_1 @ 
% 0.19/0.54           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.19/0.54           (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['2', '11'])).
% 0.19/0.54  thf('47', plain,
% 0.19/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.19/0.54         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('clc', [status(thm)], ['45', '46'])).
% 0.19/0.54  thf('48', plain,
% 0.19/0.54      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.19/0.54        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('49', plain,
% 0.19/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('split', [status(esa)], ['48'])).
% 0.19/0.54  thf('50', plain,
% 0.19/0.54      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.19/0.54         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.19/0.54             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('sup+', [status(thm)], ['47', '49'])).
% 0.19/0.54  thf('51', plain, (![X6 : $i]: ~ (v1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.19/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.19/0.54  thf('52', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.19/0.54      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.54  thf('53', plain, (![X6 : $i]: ~ (v1_subset_1 @ X6 @ X6)),
% 0.19/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.54  thf('54', plain,
% 0.19/0.54      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.19/0.54       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['50', '53'])).
% 0.19/0.54  thf('55', plain,
% 0.19/0.54      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.19/0.54       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('split', [status(esa)], ['48'])).
% 0.19/0.54  thf('56', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('57', plain,
% 0.19/0.54      (![X24 : $i, X25 : $i]:
% 0.19/0.54         (((X25) = (X24))
% 0.19/0.54          | (v1_subset_1 @ X25 @ X24)
% 0.19/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.19/0.54  thf('58', plain,
% 0.19/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.19/0.54  thf('59', plain,
% 0.19/0.54      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('60', plain,
% 0.19/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.19/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.54  thf(d11_yellow_0, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_orders_2 @ A ) =>
% 0.19/0.54       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.19/0.54  thf('61', plain,
% 0.19/0.54      (![X15 : $i]:
% 0.19/0.54         (((k3_yellow_0 @ X15) = (k1_yellow_0 @ X15 @ k1_xboole_0))
% 0.19/0.54          | ~ (l1_orders_2 @ X15))),
% 0.19/0.54      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.19/0.54  thf(dt_k1_yellow_0, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( l1_orders_2 @ A ) =>
% 0.19/0.54       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.19/0.54  thf('62', plain,
% 0.19/0.54      (![X16 : $i, X17 : $i]:
% 0.19/0.54         (~ (l1_orders_2 @ X16)
% 0.19/0.54          | (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 0.19/0.54      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.19/0.54  thf('63', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 0.19/0.54          | ~ (l1_orders_2 @ X0)
% 0.19/0.54          | ~ (l1_orders_2 @ X0))),
% 0.19/0.54      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.54  thf('64', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_orders_2 @ X0)
% 0.19/0.54          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['63'])).
% 0.19/0.54  thf(t2_subset, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.54  thf('65', plain,
% 0.19/0.54      (![X7 : $i, X8 : $i]:
% 0.19/0.54         ((r2_hidden @ X7 @ X8)
% 0.19/0.54          | (v1_xboole_0 @ X8)
% 0.19/0.54          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.19/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.54  thf('66', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_orders_2 @ X0)
% 0.19/0.54          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.19/0.54          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.54  thf('67', plain,
% 0.19/0.54      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.19/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.54         | ~ (l1_orders_2 @ sk_A)))
% 0.19/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('sup+', [status(thm)], ['60', '66'])).
% 0.19/0.54  thf('68', plain,
% 0.19/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.19/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.54  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('70', plain,
% 0.19/0.54      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 0.19/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.19/0.54  thf('71', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('72', plain,
% 0.19/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.19/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.54      inference('clc', [status(thm)], ['70', '71'])).
% 0.19/0.54  thf('73', plain,
% 0.19/0.54      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.19/0.54         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.54      inference('split', [status(esa)], ['48'])).
% 0.19/0.54  thf('74', plain,
% 0.19/0.54      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.19/0.54       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.19/0.54  thf('75', plain, ($false),
% 0.19/0.54      inference('sat_resolution*', [status(thm)], ['1', '54', '55', '74'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
