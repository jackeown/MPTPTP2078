%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O3uL8k0OfW

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:43 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 540 expanded)
%              Number of leaves         :   19 ( 156 expanded)
%              Depth                    :   20
%              Number of atoms          : 2647 (15436 expanded)
%              Number of equality atoms :  100 ( 405 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(t22_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k13_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ B @ D )
                      & ( r1_orders_2 @ A @ C @ D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ B @ E )
                              & ( r1_orders_2 @ A @ C @ E ) )
                           => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( D
                        = ( k13_lattice3 @ A @ B @ C ) )
                    <=> ( ( r1_orders_2 @ A @ B @ D )
                        & ( r1_orders_2 @ A @ C @ D )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                           => ( ( ( r1_orders_2 @ A @ B @ E )
                                & ( r1_orders_2 @ A @ C @ E ) )
                             => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_yellow_0])).

thf('0',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 )
      | ( sk_D
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) )
    | ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v1_lattice3 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k13_lattice3 @ X7 @ X6 @ X8 )
        = ( k10_lattice3 @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,
    ( ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(l26_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k10_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ B @ D )
                      & ( r1_orders_2 @ A @ C @ D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ B @ E )
                              & ( r1_orders_2 @ A @ C @ E ) )
                           => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( X3
       != ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( r1_orders_2 @ X2 @ X1 @ X5 )
      | ~ ( r1_orders_2 @ X2 @ X4 @ X5 )
      | ( r1_orders_2 @ X2 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X2 ) )
      | ( r1_orders_2 @ X2 @ ( k10_lattice3 @ X2 @ X1 @ X4 ) @ X5 )
      | ~ ( r1_orders_2 @ X2 @ X4 @ X5 )
      | ~ ( r1_orders_2 @ X2 @ X1 @ X5 )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X2 @ X1 @ X4 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v1_lattice3 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','28','29','30'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 ) )
   <= ( ( sk_D
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','31'])).

thf('33',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 )
      | ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( sk_D
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('34',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('36',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 ) )
   <= ( ( sk_D
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 )
   <= ( ( sk_D
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf('41',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 )
   <= ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_E_1 )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['4'])).

thf('45',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_E_1 )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,
    ( ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( X3
       != ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ( r1_orders_2 @ X2 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('49',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ( r1_orders_2 @ X2 @ X1 @ ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X2 @ X1 @ X4 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54','55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('60',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['4'])).

thf('62',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( X3
       != ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ( r1_orders_2 @ X2 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('65',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ( r1_orders_2 @ X2 @ X4 @ ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X2 @ X1 @ X4 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('76',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['4'])).

thf('78',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_E_1 )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['41'])).

thf('80',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['80'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_orders_2 @ X2 @ X1 @ X3 )
      | ~ ( r1_orders_2 @ X2 @ X4 @ X3 )
      | ( r1_orders_2 @ X2 @ X1 @ ( sk_E @ X3 @ X4 @ X1 @ X2 ) )
      | ( X3
        = ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('98',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['80'])).

thf('100',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_orders_2 @ X2 @ X1 @ X3 )
      | ~ ( r1_orders_2 @ X2 @ X4 @ X3 )
      | ( m1_subset_1 @ ( sk_E @ X3 @ X4 @ X1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( X3
        = ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_D )
        | ( m1_subset_1 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( sk_D
          = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ X0 @ sk_D )
        | ( m1_subset_1 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( sk_D
          = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['99','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('115',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) )
   <= ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('117',plain,
    ( ( ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['98','117'])).

thf('119',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('121',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['80'])).

thf('122',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_orders_2 @ X2 @ X1 @ X3 )
      | ~ ( r1_orders_2 @ X2 @ X4 @ X3 )
      | ( r1_orders_2 @ X2 @ X4 @ ( sk_E @ X3 @ X4 @ X1 @ X2 ) )
      | ( X3
        = ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','130'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['122','131'])).

thf('133',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['121','132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['120','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('136',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference(clc,[status(thm)],['119','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_orders_2 @ X2 @ X1 @ X3 )
      | ~ ( r1_orders_2 @ X2 @ X4 @ X3 )
      | ~ ( r1_orders_2 @ X2 @ X3 @ ( sk_E @ X3 @ X4 @ X1 @ X2 ) )
      | ( X3
        = ( k10_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ( ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('148',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['80'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_D
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('153',plain,
    ( ( sk_D
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('155',plain,
    ( ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('156',plain,
    ( ( sk_D
     != ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_D != sk_D )
   <= ( ( sk_D
       != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_D @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_C @ X9 )
          | ~ ( r1_orders_2 @ sk_A @ sk_B @ X9 ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_D
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','43','44','45','46','62','78','79','81','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O3uL8k0OfW
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 306 iterations in 0.183s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.41/0.62  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.41/0.62  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.41/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.62  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.41/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.41/0.62  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.41/0.62  thf(t22_yellow_0, conjecture,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62               ( ![D:$i]:
% 0.41/0.62                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62                   ( ( ( D ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.41/0.62                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.41/0.62                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.41/0.62                       ( ![E:$i]:
% 0.41/0.62                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.41/0.62                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.41/0.62                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i]:
% 0.41/0.62        ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.41/0.62          ( ![B:$i]:
% 0.41/0.62            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62              ( ![C:$i]:
% 0.41/0.62                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62                  ( ![D:$i]:
% 0.41/0.62                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62                      ( ( ( D ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.41/0.62                        ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.41/0.62                          ( r1_orders_2 @ A @ C @ D ) & 
% 0.41/0.62                          ( ![E:$i]:
% 0.41/0.62                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62                              ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.41/0.62                                  ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.41/0.62                                ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t22_yellow_0])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.41/0.62        | ((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) | 
% 0.41/0.62       (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.62      inference('split', [status(esa)], ['0'])).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X9 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.41/0.62          | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.41/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X9)
% 0.41/0.62          | ((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      ((![X9 : $i]:
% 0.41/0.62          (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.41/0.62           | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.41/0.62           | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.41/0.62           | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))) | 
% 0.41/0.62       (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.62      inference('split', [status(esa)], ['2'])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_E_1)
% 0.41/0.62        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.41/0.62        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.41/0.62        | ((sk_D) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_E_1))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_E_1)))),
% 0.44/0.62      inference('split', [status(esa)], ['4'])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_E_1)
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.44/0.62        | ((sk_D) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_E_1))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_E_1)))),
% 0.44/0.62      inference('split', [status(esa)], ['6'])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.44/0.62        | ((sk_D) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62         <= (((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('split', [status(esa)], ['8'])).
% 0.44/0.62  thf('10', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_k13_lattice3, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.44/0.62         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.44/0.62         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.44/0.62          | ~ (l1_orders_2 @ X7)
% 0.44/0.62          | ~ (v1_lattice3 @ X7)
% 0.44/0.62          | ~ (v5_orders_2 @ X7)
% 0.44/0.62          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.44/0.62          | ((k13_lattice3 @ X7 @ X6 @ X8) = (k10_lattice3 @ X7 @ X6 @ X8)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k13_lattice3 @ sk_A @ sk_B @ X0)
% 0.44/0.62            = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v1_lattice3 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.62  thf('14', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('15', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k13_lattice3 @ sk_A @ sk_B @ X0)
% 0.44/0.62            = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.44/0.62         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['10', '17'])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      ((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf(l26_lattice3, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.44/0.62         ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62           ( ![C:$i]:
% 0.44/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62               ( ![D:$i]:
% 0.44/0.62                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62                   ( ( ( D ) = ( k10_lattice3 @ A @ B @ C ) ) <=>
% 0.44/0.62                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.44/0.62                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.44/0.62                       ( ![E:$i]:
% 0.44/0.62                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.44/0.62                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.44/0.62                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ((X3) != (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X1 @ X5)
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X4 @ X5)
% 0.44/0.62          | (r1_orders_2 @ X2 @ X3 @ X5)
% 0.44/0.62          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | (v2_struct_0 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X4 : $i, X5 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X2))
% 0.44/0.62          | (r1_orders_2 @ X2 @ (k10_lattice3 @ X2 @ X1 @ X4) @ X5)
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X4 @ X5)
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X1 @ X5)
% 0.44/0.62          | ~ (m1_subset_1 @ (k10_lattice3 @ X2 @ X1 @ X4) @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      ((![X0 : $i]:
% 0.44/0.62          (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.44/0.62           | (r1_orders_2 @ sk_A @ (k10_lattice3 @ sk_A @ sk_B @ sk_C) @ X0)
% 0.44/0.62           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62           | ~ (v1_lattice3 @ sk_A)
% 0.44/0.62           | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62           | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['20', '22'])).
% 0.44/0.62  thf('24', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      ((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf('27', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('29', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('30', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      ((![X0 : $i]:
% 0.44/0.62          (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.44/0.62           | (r1_orders_2 @ sk_A @ sk_D @ X0)
% 0.44/0.62           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('demod', [status(thm)],
% 0.44/0.62                ['23', '24', '25', '26', '27', '28', '29', '30'])).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      ((((v2_struct_0 @ sk_A)
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_D @ sk_E_1)
% 0.44/0.62         | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_E_1)
% 0.44/0.62         | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_E_1)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.44/0.62             ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['9', '31'])).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      (((~ (r1_orders_2 @ sk_A @ sk_B @ sk_E_1)
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_D @ sk_E_1)
% 0.44/0.62         | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_E_1)) & 
% 0.44/0.62             ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '32'])).
% 0.44/0.62  thf('34', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(cc1_lattice3, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_orders_2 @ A ) =>
% 0.44/0.62       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_lattice3 @ X0) | ~ (v2_struct_0 @ X0) | ~ (l1_orders_2 @ X0))),
% 0.44/0.62      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.44/0.62  thf('36', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.62  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      ((((r1_orders_2 @ sk_A @ sk_D @ sk_E_1)
% 0.44/0.62         | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_E_1)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_E_1)) & 
% 0.44/0.62             ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('clc', [status(thm)], ['33', '38'])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_D @ sk_E_1))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_B @ sk_E_1)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_E_1)) & 
% 0.44/0.62             ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['5', '39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      ((~ (r1_orders_2 @ sk_A @ sk_D @ sk_E_1)
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.44/0.62        | ((sk_D) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      ((~ (r1_orders_2 @ sk_A @ sk_D @ sk_E_1))
% 0.44/0.62         <= (~ ((r1_orders_2 @ sk_A @ sk_D @ sk_E_1)))),
% 0.44/0.62      inference('split', [status(esa)], ['41'])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_D @ sk_E_1)) | 
% 0.44/0.62       ~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.44/0.62       ~ ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_E_1)) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_E_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['40', '42'])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_E_1)) | 
% 0.44/0.62       ~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D)) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.44/0.62      inference('split', [status(esa)], ['4'])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_E_1)) | 
% 0.44/0.62       ~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D)) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.44/0.62      inference('split', [status(esa)], ['6'])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))) | 
% 0.44/0.62       ~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D)) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.44/0.62      inference('split', [status(esa)], ['8'])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      ((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ((X3) != (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | (r1_orders_2 @ X2 @ X1 @ X3)
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | (v2_struct_0 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | (r1_orders_2 @ X2 @ X1 @ (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | ~ (m1_subset_1 @ (k10_lattice3 @ X2 @ X1 @ X4) @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['48'])).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      (((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_B @ (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62         | ~ (v1_lattice3 @ sk_A)
% 0.44/0.62         | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62         | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['47', '49'])).
% 0.44/0.62  thf('51', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('53', plain,
% 0.44/0.62      ((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf('54', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('56', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('58', plain,
% 0.44/0.62      ((((r1_orders_2 @ sk_A @ sk_B @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('demod', [status(thm)],
% 0.44/0.62                ['50', '51', '52', '53', '54', '55', '56', '57'])).
% 0.44/0.62  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('60', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('clc', [status(thm)], ['58', '59'])).
% 0.44/0.62  thf('61', plain,
% 0.44/0.62      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.44/0.62         <= (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['4'])).
% 0.44/0.62  thf('62', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) | 
% 0.44/0.62       ~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.62  thf('63', plain,
% 0.44/0.62      ((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf('64', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ((X3) != (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | (r1_orders_2 @ X2 @ X4 @ X3)
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | (v2_struct_0 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.44/0.62  thf('65', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | (r1_orders_2 @ X2 @ X4 @ (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | ~ (m1_subset_1 @ (k10_lattice3 @ X2 @ X1 @ X4) @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['64'])).
% 0.44/0.62  thf('66', plain,
% 0.44/0.62      (((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_C @ (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62         | ~ (v1_lattice3 @ sk_A)
% 0.44/0.62         | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62         | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['63', '65'])).
% 0.44/0.62  thf('67', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('69', plain,
% 0.44/0.62      ((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf('70', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('71', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('72', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('73', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('74', plain,
% 0.44/0.62      ((((r1_orders_2 @ sk_A @ sk_C @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('demod', [status(thm)],
% 0.44/0.62                ['66', '67', '68', '69', '70', '71', '72', '73'])).
% 0.44/0.62  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('76', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62         <= ((((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('clc', [status(thm)], ['74', '75'])).
% 0.44/0.62  thf('77', plain,
% 0.44/0.62      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62         <= (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['4'])).
% 0.44/0.62  thf('78', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.44/0.62       ~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['76', '77'])).
% 0.44/0.62  thf('79', plain,
% 0.44/0.62      (~ ((r1_orders_2 @ sk_A @ sk_D @ sk_E_1)) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D)) | 
% 0.44/0.62       ~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('split', [status(esa)], ['41'])).
% 0.44/0.62  thf('80', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.44/0.62        | ((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('81', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.44/0.62       (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('split', [status(esa)], ['80'])).
% 0.44/0.62  thf('82', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('83', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['80'])).
% 0.44/0.62  thf('84', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('85', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('86', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('87', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X1 @ X3)
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X4 @ X3)
% 0.44/0.62          | (r1_orders_2 @ X2 @ X1 @ (sk_E @ X3 @ X4 @ X1 @ X2))
% 0.44/0.62          | ((X3) = (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | (v2_struct_0 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.44/0.62  thf('88', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v1_lattice3 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['86', '87'])).
% 0.44/0.62  thf('89', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('90', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('92', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.44/0.62  thf('93', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.44/0.62          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.44/0.62          | ((X0) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62          | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['85', '92'])).
% 0.44/0.62  thf('94', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62        | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['84', '93'])).
% 0.44/0.62  thf('95', plain,
% 0.44/0.62      (((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (v2_struct_0 @ sk_A))) <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['83', '94'])).
% 0.44/0.62  thf('96', plain,
% 0.44/0.62      ((((v2_struct_0 @ sk_A)
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['82', '95'])).
% 0.44/0.62  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('98', plain,
% 0.44/0.62      ((((r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('clc', [status(thm)], ['96', '97'])).
% 0.44/0.62  thf('99', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['80'])).
% 0.44/0.62  thf('100', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('102', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X1 @ X3)
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X4 @ X3)
% 0.44/0.62          | (m1_subset_1 @ (sk_E @ X3 @ X4 @ X1 @ X2) @ (u1_struct_0 @ X2))
% 0.44/0.62          | ((X3) = (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | (v2_struct_0 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.44/0.62  thf('103', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v1_lattice3 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | (m1_subset_1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ 
% 0.44/0.62             (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['101', '102'])).
% 0.44/0.62  thf('104', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('105', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('106', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('107', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | (m1_subset_1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ 
% 0.44/0.62             (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.44/0.62  thf('108', plain,
% 0.44/0.62      ((![X0 : $i]:
% 0.44/0.62          (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ X0 @ sk_D)
% 0.44/0.62           | (m1_subset_1 @ (sk_E @ sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.44/0.62              (u1_struct_0 @ sk_A))
% 0.44/0.62           | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['100', '107'])).
% 0.44/0.62  thf('109', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('110', plain,
% 0.44/0.62      ((![X0 : $i]:
% 0.44/0.62          (~ (r1_orders_2 @ sk_A @ X0 @ sk_D)
% 0.44/0.62           | (m1_subset_1 @ (sk_E @ sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.44/0.62              (u1_struct_0 @ sk_A))
% 0.44/0.62           | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)))),
% 0.44/0.62      inference('demod', [status(thm)], ['108', '109'])).
% 0.44/0.62  thf('111', plain,
% 0.44/0.62      ((((v2_struct_0 @ sk_A)
% 0.44/0.62         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.44/0.62            (u1_struct_0 @ sk_A))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['99', '110'])).
% 0.44/0.62  thf('112', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('113', plain,
% 0.44/0.62      ((((v2_struct_0 @ sk_A)
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.44/0.62            (u1_struct_0 @ sk_A))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('demod', [status(thm)], ['111', '112'])).
% 0.44/0.62  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('115', plain,
% 0.44/0.62      ((((m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.44/0.62          (u1_struct_0 @ sk_A))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('clc', [status(thm)], ['113', '114'])).
% 0.44/0.62  thf('116', plain,
% 0.44/0.62      ((![X9 : $i]:
% 0.44/0.62          (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ sk_B @ X9)))
% 0.44/0.62         <= ((![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('split', [status(esa)], ['2'])).
% 0.44/0.62  thf('117', plain,
% 0.44/0.62      (((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | ~ (r1_orders_2 @ sk_A @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['115', '116'])).
% 0.44/0.62  thf('118', plain,
% 0.44/0.62      (((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | ~ (r1_orders_2 @ sk_A @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['98', '117'])).
% 0.44/0.62  thf('119', plain,
% 0.44/0.62      (((~ (r1_orders_2 @ sk_A @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['118'])).
% 0.44/0.62  thf('120', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('121', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['80'])).
% 0.44/0.62  thf('122', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('123', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('124', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('125', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X1 @ X3)
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X4 @ X3)
% 0.44/0.62          | (r1_orders_2 @ X2 @ X4 @ (sk_E @ X3 @ X4 @ X1 @ X2))
% 0.44/0.62          | ((X3) = (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | (v2_struct_0 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.44/0.62  thf('126', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v1_lattice3 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | (r1_orders_2 @ sk_A @ X0 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['124', '125'])).
% 0.44/0.62  thf('127', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('128', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('129', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('130', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | (r1_orders_2 @ sk_A @ X0 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.44/0.62  thf('131', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.44/0.62          | (r1_orders_2 @ sk_A @ sk_C @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.44/0.62          | ((X0) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62          | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['123', '130'])).
% 0.44/0.62  thf('132', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62        | (r1_orders_2 @ sk_A @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.44/0.62        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['122', '131'])).
% 0.44/0.62  thf('133', plain,
% 0.44/0.62      (((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (v2_struct_0 @ sk_A))) <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['121', '132'])).
% 0.44/0.62  thf('134', plain,
% 0.44/0.62      ((((v2_struct_0 @ sk_A)
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['120', '133'])).
% 0.44/0.62  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('136', plain,
% 0.44/0.62      ((((r1_orders_2 @ sk_A @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('clc', [status(thm)], ['134', '135'])).
% 0.44/0.62  thf('137', plain,
% 0.44/0.62      (((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (r1_orders_2 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('clc', [status(thm)], ['119', '136'])).
% 0.44/0.62  thf('138', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('139', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X1 @ X3)
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X4 @ X3)
% 0.44/0.62          | ~ (r1_orders_2 @ X2 @ X3 @ (sk_E @ X3 @ X4 @ X1 @ X2))
% 0.44/0.62          | ((X3) = (k10_lattice3 @ X2 @ X1 @ X4))
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.44/0.62          | ~ (l1_orders_2 @ X2)
% 0.44/0.62          | ~ (v1_lattice3 @ X2)
% 0.44/0.62          | ~ (v5_orders_2 @ X2)
% 0.44/0.62          | (v2_struct_0 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.44/0.62  thf('140', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v1_lattice3 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['138', '139'])).
% 0.44/0.62  thf('141', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('142', plain, ((v1_lattice3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('143', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('144', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.44/0.62  thf('145', plain,
% 0.44/0.62      (((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.44/0.62         | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.44/0.62         | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['137', '144'])).
% 0.44/0.62  thf('146', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('147', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('148', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.44/0.62      inference('split', [status(esa)], ['80'])).
% 0.44/0.62  thf('149', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('150', plain,
% 0.44/0.62      (((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.44/0.62         | (v2_struct_0 @ sk_A)))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 0.44/0.62  thf('151', plain,
% 0.44/0.62      ((((v2_struct_0 @ sk_A) | ((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['150'])).
% 0.44/0.62  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('153', plain,
% 0.44/0.62      ((((sk_D) = (k10_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('clc', [status(thm)], ['151', '152'])).
% 0.44/0.62  thf('154', plain,
% 0.44/0.62      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.44/0.62         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['10', '17'])).
% 0.44/0.62  thf('155', plain,
% 0.44/0.62      ((((sk_D) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= (~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('split', [status(esa)], ['4'])).
% 0.44/0.62  thf('156', plain,
% 0.44/0.62      ((((sk_D) != (k10_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.44/0.62         <= (~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['154', '155'])).
% 0.44/0.62  thf('157', plain,
% 0.44/0.62      ((((sk_D) != (sk_D)))
% 0.44/0.62         <= (~ (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_B @ sk_D)) & 
% 0.44/0.62             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.44/0.62             (![X9 : $i]:
% 0.44/0.62                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62                 | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62                 | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['153', '156'])).
% 0.44/0.62  thf('158', plain,
% 0.44/0.62      (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.44/0.62       ~
% 0.44/0.62       (![X9 : $i]:
% 0.44/0.62          (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | (r1_orders_2 @ sk_A @ sk_D @ X9)
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ sk_C @ X9)
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ sk_B @ X9))) | 
% 0.44/0.62       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D)) | 
% 0.44/0.62       (((sk_D) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['157'])).
% 0.44/0.62  thf('159', plain, ($false),
% 0.44/0.62      inference('sat_resolution*', [status(thm)],
% 0.44/0.62                ['1', '3', '43', '44', '45', '46', '62', '78', '79', '81', 
% 0.44/0.62                 '158'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
