%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1657+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qylkKsweyT

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:56 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 344 expanded)
%              Number of leaves         :   16 (  97 expanded)
%              Depth                    :   21
%              Number of atoms          : 1486 (5711 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_waybel_0_type,type,(
    k4_waybel_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t37_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_yellow_0 @ A @ B )
          <=> ( r2_yellow_0 @ A @ ( k4_waybel_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_yellow_0 @ A @ B )
            <=> ( r2_yellow_0 @ A @ ( k4_waybel_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_waybel_0])).

thf('0',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(t48_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r1_lattice3 @ A @ B @ D )
                <=> ( r1_lattice3 @ A @ C @ D ) ) )
            & ( r2_yellow_0 @ A @ B ) )
         => ( r2_yellow_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X5 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ( r1_lattice3 @ X3 @ X5 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ( r1_lattice3 @ X3 @ X4 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattice3 @ A @ B @ C )
              <=> ( r1_lattice3 @ A @ ( k4_waybel_0 @ A @ B ) @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r1_lattice3 @ X1 @ ( k4_waybel_0 @ X1 @ X0 ) @ X2 )
      | ( r1_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r1_lattice3 @ X1 @ X0 @ X2 )
      | ( r1_lattice3 @ X1 @ ( k4_waybel_0 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ~ ( r1_lattice3 @ X3 @ X5 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r1_lattice3 @ X3 @ X4 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('41',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['38','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
   <= ~ ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('54',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X5 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ( r1_lattice3 @ X3 @ X5 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ( r1_lattice3 @ X3 @ X4 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( r2_yellow_0 @ sk_A @ X0 )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ~ ( r1_lattice3 @ X3 @ X5 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r1_lattice3 @ X3 @ X4 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('82',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('85',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('88',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B )
   <= ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','52','53','92'])).


%------------------------------------------------------------------------------
