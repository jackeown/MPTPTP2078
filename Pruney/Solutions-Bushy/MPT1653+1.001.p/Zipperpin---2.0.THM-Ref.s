%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1653+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z69FyEJ5zu

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
% Statistics : Number of formulae       :   70 ( 182 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  756 (3180 expanded)
%              Number of equality atoms :   23 ( 115 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k3_waybel_0_type,type,(
    k3_waybel_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t33_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( k1_yellow_0 @ A @ B )
              = ( k1_yellow_0 @ A @ ( k3_waybel_0 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r1_yellow_0 @ A @ B )
             => ( ( k1_yellow_0 @ A @ B )
                = ( k1_yellow_0 @ A @ ( k3_waybel_0 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_waybel_0])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ( r1_yellow_0 @ A @ B )
            & ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_lattice3 @ A @ B @ D )
                <=> ( r2_lattice3 @ A @ C @ D ) ) ) )
         => ( ( k1_yellow_0 @ A @ B )
            = ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_yellow_0 @ X3 @ X5 )
        = ( k1_yellow_0 @ X3 @ X4 ) )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X5 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_yellow_0 @ X3 @ X5 )
        = ( k1_yellow_0 @ X3 @ X4 ) )
      | ( r2_lattice3 @ X3 @ X5 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ( r2_lattice3 @ X3 @ X4 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r1_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_lattice3 @ A @ B @ C )
              <=> ( r2_lattice3 @ A @ ( k3_waybel_0 @ A @ B ) @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_lattice3 @ X1 @ ( k3_waybel_0 @ X1 @ X0 ) @ X2 )
      | ( r2_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t31_waybel_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ( k1_yellow_0 @ sk_A @ sk_B )
 != ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,(
    ( k1_yellow_0 @ sk_A @ sk_B )
 != ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_yellow_0 @ X3 @ X5 )
        = ( k1_yellow_0 @ X3 @ X4 ) )
      | ~ ( r2_lattice3 @ X3 @ X5 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r2_lattice3 @ X3 @ X4 @ ( sk_D @ X4 @ X5 @ X3 ) )
      | ~ ( r1_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_lattice3 @ X1 @ X0 @ X2 )
      | ( r2_lattice3 @ X1 @ ( k3_waybel_0 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t31_waybel_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ( k1_yellow_0 @ sk_A @ sk_B )
 != ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_lattice3 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( sk_D @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','47'])).

thf('49',plain,(
    ( k1_yellow_0 @ sk_A @ sk_B )
 != ( k1_yellow_0 @ sk_A @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).


%------------------------------------------------------------------------------
