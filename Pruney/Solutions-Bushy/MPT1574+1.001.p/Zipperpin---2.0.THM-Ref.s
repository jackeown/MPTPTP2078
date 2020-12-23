%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1574+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GZ5bj8omHT

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:49 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 727 expanded)
%              Number of leaves         :   15 ( 191 expanded)
%              Depth                    :   34
%              Number of atoms          : 1709 (14139 expanded)
%              Number of equality atoms :   47 ( 491 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(t52_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ( r2_yellow_0 @ A @ B )
            | ( r2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) )
         => ( ( k2_yellow_0 @ A @ B )
            = ( k2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ( r2_yellow_0 @ A @ B )
              | ( r2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) )
           => ( ( k2_yellow_0 @ A @ B )
              = ( k2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_yellow_0])).

thf('0',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t49_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ( r2_yellow_0 @ A @ B )
            & ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r1_lattice3 @ A @ B @ D )
                <=> ( r1_lattice3 @ A @ C @ D ) ) ) )
         => ( ( k2_yellow_0 @ A @ B )
            = ( k2_yellow_0 @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_yellow_0 @ X2 @ X4 )
        = ( k2_yellow_0 @ X2 @ X3 ) )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X4 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( r2_yellow_0 @ X2 @ X4 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_yellow_0])).

thf('3',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_yellow_0 @ X2 @ X4 )
        = ( k2_yellow_0 @ X2 @ X3 ) )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X4 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( r2_yellow_0 @ X2 @ X4 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_yellow_0])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_yellow_0 @ X2 @ X4 )
        = ( k2_yellow_0 @ X2 @ X3 ) )
      | ( r1_lattice3 @ X2 @ X4 @ ( sk_D @ X3 @ X4 @ X2 ) )
      | ( r1_lattice3 @ X2 @ X3 @ ( sk_D @ X3 @ X4 @ X2 ) )
      | ~ ( r2_yellow_0 @ X2 @ X4 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_yellow_0])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t5_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( ( r2_lattice3 @ A @ B @ C )
             => ( r2_lattice3 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) @ C ) )
            & ( ( r2_lattice3 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) @ C )
             => ( r2_lattice3 @ A @ B @ C ) )
            & ( ( r1_lattice3 @ A @ B @ C )
             => ( r1_lattice3 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) @ C ) )
            & ( ( r1_lattice3 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) @ C )
             => ( r1_lattice3 @ A @ B @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattice3 @ X6 @ X7 @ X5 )
      | ( r1_lattice3 @ X6 @ ( k3_xboole_0 @ X7 @ ( u1_struct_0 @ X6 ) ) @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('22',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ sk_B )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( ( k2_yellow_0 @ sk_A @ sk_B )
        = ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattice3 @ X6 @ ( k3_xboole_0 @ X7 @ ( u1_struct_0 @ X6 ) ) @ X5 )
      | ( r1_lattice3 @ X6 @ X7 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('33',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( ( k2_yellow_0 @ sk_A @ sk_B )
        = ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','37'])).

thf('39',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_yellow_0 @ X2 @ X4 )
        = ( k2_yellow_0 @ X2 @ X3 ) )
      | ~ ( r1_lattice3 @ X2 @ X4 @ ( sk_D @ X3 @ X4 @ X2 ) )
      | ~ ( r1_lattice3 @ X2 @ X3 @ ( sk_D @ X3 @ X4 @ X2 ) )
      | ~ ( r2_yellow_0 @ X2 @ X4 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_yellow_0])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( ( k2_yellow_0 @ sk_A @ sk_B )
        = ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_0 @ sk_A @ sk_B )
        = ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
        = ( k2_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','52'])).

thf('54',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_yellow_0 @ X2 @ X4 )
        = ( k2_yellow_0 @ X2 @ X3 ) )
      | ( r1_lattice3 @ X2 @ X4 @ ( sk_D @ X3 @ X4 @ X2 ) )
      | ( r1_lattice3 @ X2 @ X3 @ ( sk_D @ X3 @ X4 @ X2 ) )
      | ~ ( r2_yellow_0 @ X2 @ X4 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_yellow_0])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattice3 @ X6 @ X7 @ X5 )
      | ( r1_lattice3 @ X6 @ ( k3_xboole_0 @ X7 @ ( u1_struct_0 @ X6 ) ) @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('61',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
          = ( k2_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
        = ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      = ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['67'])).

thf('69',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattice3 @ X6 @ ( k3_xboole_0 @ X7 @ ( u1_struct_0 @ X6 ) ) @ X5 )
      | ( r1_lattice3 @ X6 @ X7 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('80',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_yellow_0 @ X2 @ X4 )
        = ( k2_yellow_0 @ X2 @ X3 ) )
      | ~ ( r1_lattice3 @ X2 @ X4 @ ( sk_D @ X3 @ X4 @ X2 ) )
      | ~ ( r1_lattice3 @ X2 @ X3 @ ( sk_D @ X3 @ X4 @ X2 ) )
      | ~ ( r2_yellow_0 @ X2 @ X4 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_yellow_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
    | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      = ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('85',plain,(
    r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
    | ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      = ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('87',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['78','90'])).

thf('92',plain,
    ( ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = ( k2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','91'])).

thf('93',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).


%------------------------------------------------------------------------------
