%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YMiMgGRwzm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:16 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 383 expanded)
%              Number of leaves         :   32 ( 126 expanded)
%              Depth                    :   20
%              Number of atoms          : 1190 (5306 expanded)
%              Number of equality atoms :   24 (  83 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ( v1_subset_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('3',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('11',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ( v1_subset_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

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

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( X5 = X3 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ ( k3_yellow_0 @ X12 ) @ X11 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v1_yellow_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('21',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v13_waybel_0 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ X15 @ X13 )
      | ~ ( r1_orders_2 @ X14 @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['46','53'])).

thf('55',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('56',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('58',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('61',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ X6 @ X6 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('64',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['8','62','63'])).

thf('65',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','64'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('67',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ ( k3_yellow_0 @ X12 ) @ X11 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v1_yellow_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t17_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) )
              <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('72',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ X21 @ X19 )
      | ( r2_hidden @ X21 @ ( k5_waybel_0 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) )
      | ~ ( r1_orders_2 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_orders_2 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(dt_k5_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k5_waybel_0 @ X0 @ ( k3_yellow_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','86'])).

thf('88',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('93',plain,(
    ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['8','62'])).

thf('94',plain,(
    ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['91','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YMiMgGRwzm
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.63  % Solved by: fo/fo7.sh
% 0.41/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.63  % done 228 iterations in 0.173s
% 0.41/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.63  % SZS output start Refutation
% 0.41/0.63  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.41/0.63  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.41/0.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.41/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.41/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.41/0.63  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.41/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.63  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.41/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.63  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 0.41/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.63  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.41/0.63  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.41/0.63  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.41/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.41/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.63  thf(t8_waybel_7, conjecture,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.41/0.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.41/0.63         ( l1_orders_2 @ A ) ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.41/0.63             ( v13_waybel_0 @ B @ A ) & 
% 0.41/0.63             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.63           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.41/0.63             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.41/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.63    (~( ![A:$i]:
% 0.41/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.41/0.63            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.41/0.63            ( l1_orders_2 @ A ) ) =>
% 0.41/0.63          ( ![B:$i]:
% 0.41/0.63            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.41/0.63                ( v13_waybel_0 @ B @ A ) & 
% 0.41/0.63                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.63              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.41/0.63                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.41/0.63    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.41/0.63  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('1', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(d7_subset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.63       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.41/0.63  thf('2', plain,
% 0.41/0.63      (![X22 : $i, X23 : $i]:
% 0.41/0.63         (((X23) = (X22))
% 0.41/0.63          | (v1_subset_1 @ X23 @ X22)
% 0.41/0.63          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.41/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.41/0.63  thf('3', plain,
% 0.41/0.63      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.41/0.63        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.63  thf('4', plain,
% 0.41/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.41/0.63        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('5', plain,
% 0.41/0.63      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('split', [status(esa)], ['4'])).
% 0.41/0.63  thf('6', plain,
% 0.41/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['3', '5'])).
% 0.41/0.63  thf('7', plain,
% 0.41/0.63      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.41/0.63        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('8', plain,
% 0.41/0.63      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.41/0.63       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('split', [status(esa)], ['7'])).
% 0.41/0.63  thf('9', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(rc3_subset_1, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ?[B:$i]:
% 0.41/0.63       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.41/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.41/0.63  thf('10', plain,
% 0.41/0.63      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.41/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.41/0.63  thf('11', plain,
% 0.41/0.63      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.41/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.41/0.63  thf('12', plain,
% 0.41/0.63      (![X22 : $i, X23 : $i]:
% 0.41/0.63         (((X23) = (X22))
% 0.41/0.63          | (v1_subset_1 @ X23 @ X22)
% 0.41/0.63          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.41/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.41/0.63  thf('13', plain,
% 0.41/0.63      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.63  thf('14', plain, (![X6 : $i]: ~ (v1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.41/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.41/0.63  thf('15', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.41/0.63      inference('clc', [status(thm)], ['13', '14'])).
% 0.41/0.63  thf('16', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.41/0.63      inference('demod', [status(thm)], ['10', '15'])).
% 0.41/0.63  thf(t8_subset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.63       ( ![C:$i]:
% 0.41/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.63           ( ( ![D:$i]:
% 0.41/0.63               ( ( m1_subset_1 @ D @ A ) =>
% 0.41/0.63                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.41/0.63             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.41/0.63  thf('17', plain,
% 0.41/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.41/0.63          | ((X5) = (X3))
% 0.41/0.63          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 0.41/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.41/0.63      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.41/0.63  thf('18', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.41/0.63          | ((X1) = (X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.63  thf('19', plain,
% 0.41/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.41/0.63        | (m1_subset_1 @ 
% 0.41/0.63           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.41/0.63           (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['9', '18'])).
% 0.41/0.63  thf(t44_yellow_0, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.41/0.63         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.63           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.41/0.63  thf('20', plain,
% 0.41/0.63      (![X11 : $i, X12 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.41/0.63          | (r1_orders_2 @ X12 @ (k3_yellow_0 @ X12) @ X11)
% 0.41/0.63          | ~ (l1_orders_2 @ X12)
% 0.41/0.63          | ~ (v1_yellow_0 @ X12)
% 0.41/0.63          | ~ (v5_orders_2 @ X12)
% 0.41/0.63          | (v2_struct_0 @ X12))),
% 0.41/0.63      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.41/0.63  thf('21', plain,
% 0.41/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.41/0.63        | (v2_struct_0 @ sk_A)
% 0.41/0.63        | ~ (v5_orders_2 @ sk_A)
% 0.41/0.63        | ~ (v1_yellow_0 @ sk_A)
% 0.41/0.63        | ~ (l1_orders_2 @ sk_A)
% 0.41/0.63        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.41/0.63           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.63  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('23', plain, ((v1_yellow_0 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('25', plain,
% 0.41/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.41/0.63        | (v2_struct_0 @ sk_A)
% 0.41/0.63        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.41/0.63           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.41/0.63  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('27', plain,
% 0.41/0.63      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.41/0.63         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.63        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('clc', [status(thm)], ['25', '26'])).
% 0.41/0.63  thf('28', plain,
% 0.41/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('split', [status(esa)], ['4'])).
% 0.41/0.63  thf('29', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(l3_subset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.41/0.63  thf('30', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.63          | (r2_hidden @ X0 @ X2)
% 0.41/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.41/0.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.41/0.63  thf('31', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.63  thf('32', plain,
% 0.41/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['28', '31'])).
% 0.41/0.63  thf('33', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.41/0.63      inference('demod', [status(thm)], ['10', '15'])).
% 0.41/0.63  thf(t4_subset, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.41/0.63       ( m1_subset_1 @ A @ C ) ))).
% 0.41/0.63  thf('34', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X7 @ X8)
% 0.41/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.41/0.63          | (m1_subset_1 @ X7 @ X9))),
% 0.41/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.63  thf('35', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.63  thf('36', plain,
% 0.41/0.63      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['32', '35'])).
% 0.41/0.63  thf('37', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(d20_waybel_0, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( l1_orders_2 @ A ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.63           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.41/0.63             ( ![C:$i]:
% 0.41/0.63               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.63                 ( ![D:$i]:
% 0.41/0.63                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.63                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.41/0.63                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.63  thf('38', plain,
% 0.41/0.63      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.41/0.63          | ~ (v13_waybel_0 @ X13 @ X14)
% 0.41/0.63          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.41/0.63          | (r2_hidden @ X15 @ X13)
% 0.41/0.63          | ~ (r1_orders_2 @ X14 @ X16 @ X15)
% 0.41/0.63          | ~ (r2_hidden @ X16 @ X13)
% 0.41/0.63          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.41/0.63          | ~ (l1_orders_2 @ X14))),
% 0.41/0.63      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.41/0.63  thf('39', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ sk_A)
% 0.41/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.63          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.63          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.41/0.63          | (r2_hidden @ X1 @ sk_B_1)
% 0.41/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.41/0.63          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.63  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('41', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('42', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.63          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.63          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.41/0.63          | (r2_hidden @ X1 @ sk_B_1)
% 0.41/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.41/0.63  thf('43', plain,
% 0.41/0.63      ((![X0 : $i]:
% 0.41/0.63          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.63           | (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.63           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.41/0.63           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['36', '42'])).
% 0.41/0.63  thf('44', plain,
% 0.41/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('split', [status(esa)], ['4'])).
% 0.41/0.63  thf('45', plain,
% 0.41/0.63      ((![X0 : $i]:
% 0.41/0.63          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.63           | (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.63           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.63  thf('46', plain,
% 0.41/0.63      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.41/0.63         | (r2_hidden @ 
% 0.41/0.63            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.41/0.63            sk_B_1)
% 0.41/0.63         | ~ (m1_subset_1 @ 
% 0.41/0.63              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.41/0.63              (u1_struct_0 @ sk_A))))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['27', '45'])).
% 0.41/0.63  thf('47', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('48', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.41/0.63      inference('demod', [status(thm)], ['10', '15'])).
% 0.41/0.63  thf('49', plain,
% 0.41/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.41/0.63          | ((X5) = (X3))
% 0.41/0.63          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.41/0.63          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.41/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.41/0.63      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.41/0.63  thf('50', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.41/0.63          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.41/0.63          | ((X1) = (X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.63  thf('51', plain,
% 0.41/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.41/0.63        | ~ (r2_hidden @ 
% 0.41/0.63             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.41/0.63             sk_B_1)
% 0.41/0.63        | ~ (r2_hidden @ 
% 0.41/0.63             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.41/0.63             (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['47', '50'])).
% 0.41/0.63  thf('52', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.63  thf('53', plain,
% 0.41/0.63      ((~ (r2_hidden @ 
% 0.41/0.63           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.41/0.63           sk_B_1)
% 0.41/0.63        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('clc', [status(thm)], ['51', '52'])).
% 0.41/0.63  thf('54', plain,
% 0.41/0.63      (((~ (m1_subset_1 @ 
% 0.41/0.63            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.41/0.63            (u1_struct_0 @ sk_A))
% 0.41/0.63         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('clc', [status(thm)], ['46', '53'])).
% 0.41/0.63  thf('55', plain,
% 0.41/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.41/0.63        | (m1_subset_1 @ 
% 0.41/0.63           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.41/0.63           (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['9', '18'])).
% 0.41/0.63  thf('56', plain,
% 0.41/0.63      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('clc', [status(thm)], ['54', '55'])).
% 0.41/0.63  thf('57', plain,
% 0.41/0.63      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('split', [status(esa)], ['7'])).
% 0.41/0.63  thf('58', plain,
% 0.41/0.63      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.41/0.63         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.41/0.63             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['56', '57'])).
% 0.41/0.63  thf('59', plain, (![X6 : $i]: ~ (v1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.41/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.41/0.63  thf('60', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.41/0.63      inference('clc', [status(thm)], ['13', '14'])).
% 0.41/0.63  thf('61', plain, (![X6 : $i]: ~ (v1_subset_1 @ X6 @ X6)),
% 0.41/0.63      inference('demod', [status(thm)], ['59', '60'])).
% 0.41/0.63  thf('62', plain,
% 0.41/0.63      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.41/0.63       ~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['58', '61'])).
% 0.41/0.63  thf('63', plain,
% 0.41/0.63      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.41/0.63       ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))),
% 0.41/0.63      inference('split', [status(esa)], ['4'])).
% 0.41/0.63  thf('64', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['8', '62', '63'])).
% 0.41/0.63  thf('65', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.41/0.63      inference('simpl_trail', [status(thm)], ['6', '64'])).
% 0.41/0.63  thf(dt_k3_yellow_0, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( l1_orders_2 @ A ) =>
% 0.41/0.63       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.41/0.63  thf('66', plain,
% 0.41/0.63      (![X10 : $i]:
% 0.41/0.63         ((m1_subset_1 @ (k3_yellow_0 @ X10) @ (u1_struct_0 @ X10))
% 0.41/0.63          | ~ (l1_orders_2 @ X10))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.41/0.63  thf('67', plain,
% 0.41/0.63      (![X10 : $i]:
% 0.41/0.63         ((m1_subset_1 @ (k3_yellow_0 @ X10) @ (u1_struct_0 @ X10))
% 0.41/0.63          | ~ (l1_orders_2 @ X10))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.41/0.63  thf('68', plain,
% 0.41/0.63      (![X11 : $i, X12 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.41/0.63          | (r1_orders_2 @ X12 @ (k3_yellow_0 @ X12) @ X11)
% 0.41/0.63          | ~ (l1_orders_2 @ X12)
% 0.41/0.63          | ~ (v1_yellow_0 @ X12)
% 0.41/0.63          | ~ (v5_orders_2 @ X12)
% 0.41/0.63          | (v2_struct_0 @ X12))),
% 0.41/0.63      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.41/0.63  thf('69', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (v5_orders_2 @ X0)
% 0.41/0.63          | ~ (v1_yellow_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0)
% 0.41/0.63          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k3_yellow_0 @ X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.41/0.63  thf('70', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k3_yellow_0 @ X0))
% 0.41/0.63          | ~ (v1_yellow_0 @ X0)
% 0.41/0.63          | ~ (v5_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0))),
% 0.41/0.63      inference('simplify', [status(thm)], ['69'])).
% 0.41/0.63  thf('71', plain,
% 0.41/0.63      (![X10 : $i]:
% 0.41/0.63         ((m1_subset_1 @ (k3_yellow_0 @ X10) @ (u1_struct_0 @ X10))
% 0.41/0.63          | ~ (l1_orders_2 @ X10))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.41/0.63  thf(t17_waybel_0, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.63           ( ![C:$i]:
% 0.41/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.63               ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) ) <=>
% 0.41/0.63                 ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.63  thf('72', plain,
% 0.41/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.41/0.63          | ~ (r1_orders_2 @ X20 @ X21 @ X19)
% 0.41/0.63          | (r2_hidden @ X21 @ (k5_waybel_0 @ X20 @ X19))
% 0.41/0.63          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.41/0.63          | ~ (l1_orders_2 @ X20)
% 0.41/0.63          | (v2_struct_0 @ X20))),
% 0.41/0.63      inference('cnf', [status(esa)], [t17_waybel_0])).
% 0.41/0.63  thf('73', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0)
% 0.41/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.63          | (r2_hidden @ X1 @ (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0)))
% 0.41/0.63          | ~ (r1_orders_2 @ X0 @ X1 @ (k3_yellow_0 @ X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['71', '72'])).
% 0.41/0.63  thf('74', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r1_orders_2 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 0.41/0.63          | (r2_hidden @ X1 @ (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0)))
% 0.41/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0))),
% 0.41/0.63      inference('simplify', [status(thm)], ['73'])).
% 0.41/0.63  thf('75', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (v5_orders_2 @ X0)
% 0.41/0.63          | ~ (v1_yellow_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 0.41/0.63          | (r2_hidden @ (k3_yellow_0 @ X0) @ 
% 0.41/0.63             (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['70', '74'])).
% 0.41/0.63  thf('76', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((r2_hidden @ (k3_yellow_0 @ X0) @ 
% 0.41/0.63           (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0)))
% 0.41/0.63          | ~ (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 0.41/0.63          | ~ (v1_yellow_0 @ X0)
% 0.41/0.63          | ~ (v5_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0))),
% 0.41/0.63      inference('simplify', [status(thm)], ['75'])).
% 0.41/0.63  thf('77', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (v5_orders_2 @ X0)
% 0.41/0.63          | ~ (v1_yellow_0 @ X0)
% 0.41/0.63          | (r2_hidden @ (k3_yellow_0 @ X0) @ 
% 0.41/0.63             (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['66', '76'])).
% 0.41/0.63  thf('78', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((r2_hidden @ (k3_yellow_0 @ X0) @ 
% 0.41/0.63           (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0)))
% 0.41/0.63          | ~ (v1_yellow_0 @ X0)
% 0.41/0.63          | ~ (v5_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0))),
% 0.41/0.63      inference('simplify', [status(thm)], ['77'])).
% 0.41/0.63  thf('79', plain,
% 0.41/0.63      (![X10 : $i]:
% 0.41/0.63         ((m1_subset_1 @ (k3_yellow_0 @ X10) @ (u1_struct_0 @ X10))
% 0.41/0.63          | ~ (l1_orders_2 @ X10))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.41/0.63  thf(dt_k5_waybel_0, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.41/0.63         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.63       ( m1_subset_1 @
% 0.41/0.63         ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.63  thf('80', plain,
% 0.41/0.63      (![X17 : $i, X18 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ X17)
% 0.41/0.63          | (v2_struct_0 @ X17)
% 0.41/0.63          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.41/0.63          | (m1_subset_1 @ (k5_waybel_0 @ X17 @ X18) @ 
% 0.41/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k5_waybel_0])).
% 0.41/0.63  thf('81', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ X0)
% 0.41/0.63          | (m1_subset_1 @ (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0)) @ 
% 0.41/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['79', '80'])).
% 0.41/0.63  thf('82', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((v2_struct_0 @ X0)
% 0.41/0.63          | (m1_subset_1 @ (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0)) @ 
% 0.41/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.63          | ~ (l1_orders_2 @ X0))),
% 0.41/0.63      inference('simplify', [status(thm)], ['81'])).
% 0.41/0.63  thf('83', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.63          | (r2_hidden @ X0 @ X2)
% 0.41/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.41/0.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.41/0.63  thf('84', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.63          | ~ (r2_hidden @ X1 @ (k5_waybel_0 @ X0 @ (k3_yellow_0 @ X0))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.63  thf('85', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (l1_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (v5_orders_2 @ X0)
% 0.41/0.63          | ~ (v1_yellow_0 @ X0)
% 0.41/0.63          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['78', '84'])).
% 0.41/0.63  thf('86', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 0.41/0.63          | ~ (v1_yellow_0 @ X0)
% 0.41/0.63          | ~ (v5_orders_2 @ X0)
% 0.41/0.63          | (v2_struct_0 @ X0)
% 0.41/0.63          | ~ (l1_orders_2 @ X0))),
% 0.41/0.63      inference('simplify', [status(thm)], ['85'])).
% 0.41/0.63  thf('87', plain,
% 0.41/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.41/0.63        | ~ (l1_orders_2 @ sk_A)
% 0.41/0.63        | (v2_struct_0 @ sk_A)
% 0.41/0.63        | ~ (v5_orders_2 @ sk_A)
% 0.41/0.63        | ~ (v1_yellow_0 @ sk_A))),
% 0.41/0.63      inference('sup+', [status(thm)], ['65', '86'])).
% 0.41/0.63  thf('88', plain, ((l1_orders_2 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('89', plain, ((v5_orders_2 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('90', plain, ((v1_yellow_0 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('91', plain,
% 0.41/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.41/0.63  thf('92', plain,
% 0.41/0.63      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.41/0.63         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.63      inference('split', [status(esa)], ['7'])).
% 0.41/0.63  thf('93', plain, (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['8', '62'])).
% 0.41/0.63  thf('94', plain, (~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)),
% 0.41/0.63      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.41/0.63  thf('95', plain, ((v2_struct_0 @ sk_A)),
% 0.41/0.63      inference('clc', [status(thm)], ['91', '94'])).
% 0.41/0.63  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
