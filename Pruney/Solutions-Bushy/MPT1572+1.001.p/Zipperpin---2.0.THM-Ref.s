%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1572+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nQwf7gOdo2

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:48 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 554 expanded)
%              Number of leaves         :   17 ( 145 expanded)
%              Depth                    :   24
%              Number of atoms          : 3313 (14237 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(t50_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ( r2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) )
           => ( r2_yellow_0 @ A @ B ) )
          & ( ( r2_yellow_0 @ A @ B )
           => ( r2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) )
          & ( ( r1_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) )
           => ( r1_yellow_0 @ A @ B ) )
          & ( ( r1_yellow_0 @ A @ B )
           => ( r1_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ( r2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) )
             => ( r2_yellow_0 @ A @ B ) )
            & ( ( r2_yellow_0 @ A @ B )
             => ( r2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) )
            & ( ( r1_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) )
             => ( r1_yellow_0 @ A @ B ) )
            & ( ( r1_yellow_0 @ A @ B )
             => ( r1_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_yellow_0])).

thf('0',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

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

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ( m1_subset_1 @ ( sk_D_1 @ X4 @ X5 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ( r1_lattice3 @ X3 @ X5 @ ( sk_D_1 @ X4 @ X5 @ X3 ) )
      | ( r1_lattice3 @ X3 @ X4 @ ( sk_D_1 @ X4 @ X5 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_lattice3 @ X7 @ ( k3_xboole_0 @ X8 @ ( u1_struct_0 @ X7 ) ) @ X6 )
      | ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( r2_yellow_0 @ sk_A @ X0 )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ( r1_lattice3 @ X7 @ ( k3_xboole_0 @ X8 @ ( u1_struct_0 @ X7 ) ) @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('29',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ~ ( r1_lattice3 @ X3 @ X5 @ ( sk_D_1 @ X4 @ X5 @ X3 ) )
      | ~ ( r1_lattice3 @ X3 @ X4 @ ( sk_D_1 @ X4 @ X5 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('37',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('40',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('43',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B )
   <= ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('47',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ( m1_subset_1 @ ( sk_D_1 @ X4 @ X5 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('56',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ( r1_lattice3 @ X3 @ X5 @ ( sk_D_1 @ X4 @ X5 @ X3 ) )
      | ( r1_lattice3 @ X3 @ X4 @ ( sk_D_1 @ X4 @ X5 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('61',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ( r1_lattice3 @ X7 @ ( k3_xboole_0 @ X8 @ ( u1_struct_0 @ X7 ) ) @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('62',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r2_yellow_0 @ sk_A @ X0 )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        | ( r2_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(eq_fact,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_lattice3 @ X7 @ ( k3_xboole_0 @ X8 @ ( u1_struct_0 @ X7 ) ) @ X6 )
      | ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('71',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['54','73'])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_yellow_0 @ X3 @ X4 )
      | ~ ( r1_lattice3 @ X3 @ X5 @ ( sk_D_1 @ X4 @ X5 @ X3 ) )
      | ~ ( r1_lattice3 @ X3 @ X4 @ ( sk_D_1 @ X4 @ X5 @ X3 ) )
      | ~ ( r2_yellow_0 @ X3 @ X5 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('79',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('82',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D_1 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('85',plain,
    ( ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('89',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t46_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_lattice3 @ A @ B @ D )
                <=> ( r2_lattice3 @ A @ C @ D ) ) )
            & ( r1_yellow_0 @ A @ B ) )
         => ( r1_yellow_0 @ A @ C ) ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('103',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r2_lattice3 @ X7 @ X8 @ X6 )
      | ( r2_lattice3 @ X7 @ ( k3_xboole_0 @ X8 @ ( u1_struct_0 @ X7 ) ) @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('104',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(eq_fact,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r2_lattice3 @ X7 @ ( k3_xboole_0 @ X8 @ ( u1_struct_0 @ X7 ) ) @ X6 )
      | ( r2_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('113',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['96','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('121',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('127',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('131',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('133',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['133'])).

thf('135',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r2_lattice3 @ X7 @ ( k3_xboole_0 @ X8 @ ( u1_struct_0 @ X7 ) ) @ X6 )
      | ( r2_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','151'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('158',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r2_lattice3 @ X7 @ X8 @ X6 )
      | ( r2_lattice3 @ X7 @ ( k3_xboole_0 @ X8 @ ( u1_struct_0 @ X7 ) ) @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t5_yellow_0])).

thf('159',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['156','161'])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('167',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('170',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('173',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_B )
   <= ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('177',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','47','89','131','132','134','177'])).


%------------------------------------------------------------------------------
