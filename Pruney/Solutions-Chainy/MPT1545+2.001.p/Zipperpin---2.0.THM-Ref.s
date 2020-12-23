%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hdPg5cqqMx

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(t23_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k12_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ D @ B )
                      & ( r1_orders_2 @ A @ D @ C )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ E @ B )
                              & ( r1_orders_2 @ A @ E @ C ) )
                           => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( D
                        = ( k12_lattice3 @ A @ B @ C ) )
                    <=> ( ( r1_orders_2 @ A @ D @ B )
                        & ( r1_orders_2 @ A @ D @ C )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                           => ( ( ( r1_orders_2 @ A @ E @ B )
                                & ( r1_orders_2 @ A @ E @ C ) )
                             => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_yellow_0])).

thf('0',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B )
      | ( sk_D
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
        | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
        | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) )
    | ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
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

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v2_lattice3 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k12_lattice3 @ X7 @ X6 @ X8 )
        = ( k11_lattice3 @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,
    ( ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(l28_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k11_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ D @ B )
                      & ( r1_orders_2 @ A @ D @ C )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ E @ B )
                              & ( r1_orders_2 @ A @ E @ C ) )
                           => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( X3
       != ( k11_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( r1_orders_2 @ X2 @ X5 @ X1 )
      | ~ ( r1_orders_2 @ X2 @ X5 @ X4 )
      | ( r1_orders_2 @ X2 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X2 ) )
      | ( r1_orders_2 @ X2 @ X5 @ ( k11_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( r1_orders_2 @ X2 @ X5 @ X4 )
      | ~ ( r1_orders_2 @ X2 @ X5 @ X1 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X2 @ X1 @ X4 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
        | ( r1_orders_2 @ sk_A @ X0 @ ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v2_lattice3 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','28','29','30'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B ) )
   <= ( ( sk_D
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','31'])).

thf('33',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B )
      | ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( sk_D
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C )
      & ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('34',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

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
    ( ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B ) )
   <= ( ( sk_D
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C )
      & ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D )
   <= ( ( sk_D
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C )
      & ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf('41',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D )
   <= ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_B )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('45',plain,
    ( ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_C )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,
    ( ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( X3
       != ( k11_lattice3 @ X2 @ X1 @ X4 ) )
      | ( r1_orders_2 @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('49',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ( r1_orders_2 @ X2 @ ( k11_lattice3 @ X2 @ X1 @ X4 ) @ X1 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X2 @ X1 @ X4 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_B )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54','55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('60',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('62',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( X3
       != ( k11_lattice3 @ X2 @ X1 @ X4 ) )
      | ( r1_orders_2 @ X2 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('65',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ( r1_orders_2 @ X2 @ ( k11_lattice3 @ X2 @ X1 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X2 @ X1 @ X4 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('76',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
   <= ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
   <= ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('78',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_E_1 @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['41'])).

thf('80',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
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
      | ~ ( r1_orders_2 @ X2 @ X3 @ X1 )
      | ~ ( r1_orders_2 @ X2 @ X3 @ X4 )
      | ( r1_orders_2 @ X2 @ ( sk_E @ X3 @ X4 @ X1 @ X2 ) @ X1 )
      | ( X3
        = ( k11_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('98',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['80'])).

thf('100',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_orders_2 @ X2 @ X3 @ X1 )
      | ~ ( r1_orders_2 @ X2 @ X3 @ X4 )
      | ( m1_subset_1 @ ( sk_E @ X3 @ X4 @ X1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( X3
        = ( k11_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ sk_D @ X0 )
        | ( m1_subset_1 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( sk_D
          = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_D @ X0 )
        | ( m1_subset_1 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( sk_D
          = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('115',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
        | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
        | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) )
   <= ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
        | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
        | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('117',plain,
    ( ( ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','117'])).

thf('119',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('121',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
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
      | ~ ( r1_orders_2 @ X2 @ X3 @ X1 )
      | ~ ( r1_orders_2 @ X2 @ X3 @ X4 )
      | ( r1_orders_2 @ X2 @ ( sk_E @ X3 @ X4 @ X1 @ X2 ) @ X4 )
      | ( X3
        = ( k11_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','130'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['122','131'])).

thf('133',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['121','132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('136',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['119','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_orders_2 @ X2 @ X3 @ X1 )
      | ~ ( r1_orders_2 @ X2 @ X3 @ X4 )
      | ~ ( r1_orders_2 @ X2 @ ( sk_E @ X3 @ X4 @ X1 @ X2 ) @ X3 )
      | ( X3
        = ( k11_lattice3 @ X2 @ X1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ( ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('148',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['80'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_D
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('153',plain,
    ( ( sk_D
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('155',plain,
    ( ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('156',plain,
    ( ( sk_D
     != ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_D
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_D != sk_D )
   <= ( ( sk_D
       != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X9 @ sk_D )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_C )
          | ~ ( r1_orders_2 @ sk_A @ X9 @ sk_B ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_B )
    | ( sk_D
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','43','44','45','46','62','78','79','81','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hdPg5cqqMx
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.65  % Solved by: fo/fo7.sh
% 0.20/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.65  % done 306 iterations in 0.194s
% 0.20/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.65  % SZS output start Refutation
% 0.20/0.65  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.65  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.65  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.65  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.65  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.65  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.20/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.65  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.20/0.65  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.20/0.65  thf(t23_yellow_0, conjecture,
% 0.20/0.65    (![A:$i]:
% 0.20/0.65     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.65       ( ![B:$i]:
% 0.20/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65           ( ![C:$i]:
% 0.20/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65               ( ![D:$i]:
% 0.20/0.65                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65                   ( ( ( D ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.65                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.20/0.65                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.20/0.65                       ( ![E:$i]:
% 0.20/0.65                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.20/0.65                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.20/0.65                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.65    (~( ![A:$i]:
% 0.20/0.65        ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.65          ( ![B:$i]:
% 0.20/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65              ( ![C:$i]:
% 0.20/0.65                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65                  ( ![D:$i]:
% 0.20/0.65                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65                      ( ( ( D ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.65                        ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.20/0.65                          ( r1_orders_2 @ A @ D @ C ) & 
% 0.20/0.65                          ( ![E:$i]:
% 0.20/0.65                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65                              ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.20/0.65                                  ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.20/0.65                                ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.65    inference('cnf.neg', [status(esa)], [t23_yellow_0])).
% 0.20/0.65  thf('0', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_D @ sk_B)
% 0.20/0.65        | ((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('1', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) | 
% 0.20/0.65       (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('split', [status(esa)], ['0'])).
% 0.20/0.65  thf('2', plain,
% 0.20/0.65      (![X9 : $i]:
% 0.20/0.65         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.65          | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.65          | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.65          | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B)
% 0.20/0.65          | ((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('3', plain,
% 0.20/0.65      ((![X9 : $i]:
% 0.20/0.65          (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.65           | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.65           | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.65           | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))) | 
% 0.20/0.65       (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('split', [status(esa)], ['2'])).
% 0.20/0.65  thf('4', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_B)
% 0.20/0.65        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.65        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_B)
% 0.20/0.65        | ((sk_D) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('5', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_B))
% 0.20/0.65         <= (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_B)))),
% 0.20/0.65      inference('split', [status(esa)], ['4'])).
% 0.20/0.65  thf('6', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_C)
% 0.20/0.65        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.65        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_B)
% 0.20/0.65        | ((sk_D) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('7', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_C))
% 0.20/0.65         <= (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_C)))),
% 0.20/0.65      inference('split', [status(esa)], ['6'])).
% 0.20/0.65  thf('8', plain,
% 0.20/0.65      (((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.65        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.65        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_B)
% 0.20/0.65        | ((sk_D) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('9', plain,
% 0.20/0.65      (((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.65         <= (((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.65      inference('split', [status(esa)], ['8'])).
% 0.20/0.65  thf('10', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf(redefinition_k12_lattice3, axiom,
% 0.20/0.65    (![A:$i,B:$i,C:$i]:
% 0.20/0.65     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.65         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.65         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.65       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.65  thf('12', plain,
% 0.20/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.65         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.65          | ~ (l1_orders_2 @ X7)
% 0.20/0.65          | ~ (v2_lattice3 @ X7)
% 0.20/0.65          | ~ (v5_orders_2 @ X7)
% 0.20/0.65          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.65          | ((k12_lattice3 @ X7 @ X6 @ X8) = (k11_lattice3 @ X7 @ X6 @ X8)))),
% 0.20/0.65      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.20/0.65  thf('13', plain,
% 0.20/0.65      (![X0 : $i]:
% 0.20/0.65         (((k12_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.65            = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.65          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.65          | ~ (v2_lattice3 @ sk_A)
% 0.20/0.65          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.65  thf('14', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('15', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('17', plain,
% 0.20/0.65      (![X0 : $i]:
% 0.20/0.65         (((k12_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.65            = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.65      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.20/0.65  thf('18', plain,
% 0.20/0.65      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.65         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.65      inference('sup-', [status(thm)], ['10', '17'])).
% 0.20/0.65  thf('19', plain,
% 0.20/0.65      ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('split', [status(esa)], ['0'])).
% 0.20/0.65  thf('20', plain,
% 0.20/0.65      ((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.65  thf(l28_lattice3, axiom,
% 0.20/0.65    (![A:$i]:
% 0.20/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.20/0.65         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.65       ( ![B:$i]:
% 0.20/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65           ( ![C:$i]:
% 0.20/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65               ( ![D:$i]:
% 0.20/0.65                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.65                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.20/0.65                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.20/0.65                       ( ![E:$i]:
% 0.20/0.65                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.65                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.20/0.65                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.20/0.65                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.65  thf('21', plain,
% 0.20/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.65         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ((X3) != (k11_lattice3 @ X2 @ X1 @ X4))
% 0.20/0.65          | ~ (r1_orders_2 @ X2 @ X5 @ X1)
% 0.20/0.65          | ~ (r1_orders_2 @ X2 @ X5 @ X4)
% 0.20/0.65          | (r1_orders_2 @ X2 @ X5 @ X3)
% 0.20/0.65          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (l1_orders_2 @ X2)
% 0.20/0.65          | ~ (v2_lattice3 @ X2)
% 0.20/0.65          | ~ (v5_orders_2 @ X2)
% 0.20/0.65          | (v2_struct_0 @ X2))),
% 0.20/0.65      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.65  thf('22', plain,
% 0.20/0.65      (![X1 : $i, X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.65         ((v2_struct_0 @ X2)
% 0.20/0.65          | ~ (v5_orders_2 @ X2)
% 0.20/0.65          | ~ (v2_lattice3 @ X2)
% 0.20/0.65          | ~ (l1_orders_2 @ X2)
% 0.20/0.65          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X2))
% 0.20/0.65          | (r1_orders_2 @ X2 @ X5 @ (k11_lattice3 @ X2 @ X1 @ X4))
% 0.20/0.65          | ~ (r1_orders_2 @ X2 @ X5 @ X4)
% 0.20/0.65          | ~ (r1_orders_2 @ X2 @ X5 @ X1)
% 0.20/0.65          | ~ (m1_subset_1 @ (k11_lattice3 @ X2 @ X1 @ X4) @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2)))),
% 0.20/0.65      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.65  thf('23', plain,
% 0.20/0.65      ((![X0 : $i]:
% 0.20/0.65          (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.20/0.65           | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.65           | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.65           | ~ (r1_orders_2 @ sk_A @ X0 @ sk_C)
% 0.20/0.65           | (r1_orders_2 @ sk_A @ X0 @ (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.65           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.65           | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.65           | ~ (l1_orders_2 @ sk_A)
% 0.20/0.65           | ~ (v2_lattice3 @ sk_A)
% 0.20/0.65           | ~ (v5_orders_2 @ sk_A)
% 0.20/0.65           | (v2_struct_0 @ sk_A)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.65  thf('24', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('26', plain,
% 0.20/0.65      ((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.65  thf('27', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('29', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('30', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('31', plain,
% 0.20/0.65      ((![X0 : $i]:
% 0.20/0.65          (~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.65           | ~ (r1_orders_2 @ sk_A @ X0 @ sk_C)
% 0.20/0.65           | (r1_orders_2 @ sk_A @ X0 @ sk_D)
% 0.20/0.65           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.65           | (v2_struct_0 @ sk_A)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('demod', [status(thm)],
% 0.20/0.65                ['23', '24', '25', '26', '27', '28', '29', '30'])).
% 0.20/0.65  thf('32', plain,
% 0.20/0.65      ((((v2_struct_0 @ sk_A)
% 0.20/0.65         | (r1_orders_2 @ sk_A @ sk_E_1 @ sk_D)
% 0.20/0.65         | ~ (r1_orders_2 @ sk_A @ sk_E_1 @ sk_C)
% 0.20/0.65         | ~ (r1_orders_2 @ sk_A @ sk_E_1 @ sk_B)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.20/0.65             ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.65      inference('sup-', [status(thm)], ['9', '31'])).
% 0.20/0.65  thf('33', plain,
% 0.20/0.65      (((~ (r1_orders_2 @ sk_A @ sk_E_1 @ sk_B)
% 0.20/0.65         | (r1_orders_2 @ sk_A @ sk_E_1 @ sk_D)
% 0.20/0.65         | (v2_struct_0 @ sk_A)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.20/0.65             ((r1_orders_2 @ sk_A @ sk_E_1 @ sk_C)) & 
% 0.20/0.65             ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.65      inference('sup-', [status(thm)], ['7', '32'])).
% 0.20/0.65  thf('34', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf(cc2_lattice3, axiom,
% 0.20/0.65    (![A:$i]:
% 0.20/0.65     ( ( l1_orders_2 @ A ) =>
% 0.20/0.65       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.20/0.65  thf('35', plain,
% 0.20/0.65      (![X0 : $i]:
% 0.20/0.65         (~ (v2_lattice3 @ X0) | ~ (v2_struct_0 @ X0) | ~ (l1_orders_2 @ X0))),
% 0.20/0.65      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.20/0.65  thf('36', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v2_struct_0 @ sk_A))),
% 0.20/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.65  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.65  thf('39', plain,
% 0.20/0.65      ((((r1_orders_2 @ sk_A @ sk_E_1 @ sk_D)
% 0.20/0.65         | ~ (r1_orders_2 @ sk_A @ sk_E_1 @ sk_B)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.20/0.65             ((r1_orders_2 @ sk_A @ sk_E_1 @ sk_C)) & 
% 0.20/0.65             ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.65      inference('clc', [status(thm)], ['33', '38'])).
% 0.20/0.65  thf('40', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_D))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.20/0.65             ((r1_orders_2 @ sk_A @ sk_E_1 @ sk_B)) & 
% 0.20/0.65             ((r1_orders_2 @ sk_A @ sk_E_1 @ sk_C)) & 
% 0.20/0.65             ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.65      inference('sup-', [status(thm)], ['5', '39'])).
% 0.20/0.65  thf('41', plain,
% 0.20/0.65      ((~ (r1_orders_2 @ sk_A @ sk_E_1 @ sk_D)
% 0.20/0.65        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.65        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_B)
% 0.20/0.65        | ((sk_D) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('42', plain,
% 0.20/0.65      ((~ (r1_orders_2 @ sk_A @ sk_E_1 @ sk_D))
% 0.20/0.65         <= (~ ((r1_orders_2 @ sk_A @ sk_E_1 @ sk_D)))),
% 0.20/0.65      inference('split', [status(esa)], ['41'])).
% 0.20/0.65  thf('43', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_D)) | 
% 0.20/0.65       ~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.65       ~ ((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))) | 
% 0.20/0.65       ~ ((r1_orders_2 @ sk_A @ sk_E_1 @ sk_C)) | 
% 0.20/0.65       ~ ((r1_orders_2 @ sk_A @ sk_E_1 @ sk_B))),
% 0.20/0.65      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.65  thf('44', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_B)) | 
% 0.20/0.65       ~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.65       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_B)) | 
% 0.20/0.65       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_C))),
% 0.20/0.65      inference('split', [status(esa)], ['4'])).
% 0.20/0.65  thf('45', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_E_1 @ sk_C)) | 
% 0.20/0.65       ~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.65       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_B)) | 
% 0.20/0.65       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_C))),
% 0.20/0.65      inference('split', [status(esa)], ['6'])).
% 0.20/0.65  thf('46', plain,
% 0.20/0.65      (((m1_subset_1 @ sk_E_1 @ (u1_struct_0 @ sk_A))) | 
% 0.20/0.65       ~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.65       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_B)) | 
% 0.20/0.65       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_C))),
% 0.20/0.65      inference('split', [status(esa)], ['8'])).
% 0.20/0.65  thf('47', plain,
% 0.20/0.65      ((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.65  thf('48', plain,
% 0.20/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.65         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ((X3) != (k11_lattice3 @ X2 @ X1 @ X4))
% 0.20/0.65          | (r1_orders_2 @ X2 @ X3 @ X1)
% 0.20/0.65          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (l1_orders_2 @ X2)
% 0.20/0.65          | ~ (v2_lattice3 @ X2)
% 0.20/0.65          | ~ (v5_orders_2 @ X2)
% 0.20/0.65          | (v2_struct_0 @ X2))),
% 0.20/0.65      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.65  thf('49', plain,
% 0.20/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.65         ((v2_struct_0 @ X2)
% 0.20/0.65          | ~ (v5_orders_2 @ X2)
% 0.20/0.65          | ~ (v2_lattice3 @ X2)
% 0.20/0.65          | ~ (l1_orders_2 @ X2)
% 0.20/0.65          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.65          | (r1_orders_2 @ X2 @ (k11_lattice3 @ X2 @ X1 @ X4) @ X1)
% 0.20/0.65          | ~ (m1_subset_1 @ (k11_lattice3 @ X2 @ X1 @ X4) @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2)))),
% 0.20/0.65      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.65  thf('50', plain,
% 0.20/0.65      (((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.20/0.65         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.65         | (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.20/0.65         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.65         | ~ (l1_orders_2 @ sk_A)
% 0.20/0.65         | ~ (v2_lattice3 @ sk_A)
% 0.20/0.65         | ~ (v5_orders_2 @ sk_A)
% 0.20/0.65         | (v2_struct_0 @ sk_A)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('sup-', [status(thm)], ['47', '49'])).
% 0.20/0.65  thf('51', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('53', plain,
% 0.20/0.65      ((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.65  thf('54', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('56', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.65  thf('58', plain,
% 0.20/0.65      ((((r1_orders_2 @ sk_A @ sk_D @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('demod', [status(thm)],
% 0.20/0.65                ['50', '51', '52', '53', '54', '55', '56', '57'])).
% 0.20/0.65  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.65  thf('60', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.65  thf('61', plain,
% 0.20/0.65      ((~ (r1_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.20/0.65         <= (~ ((r1_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.20/0.65      inference('split', [status(esa)], ['4'])).
% 0.20/0.65  thf('62', plain,
% 0.20/0.65      (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) | 
% 0.20/0.65       ~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.65      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.65  thf('63', plain,
% 0.20/0.65      ((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.65         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.65  thf('64', plain,
% 0.20/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.65         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ((X3) != (k11_lattice3 @ X2 @ X1 @ X4))
% 0.20/0.65          | (r1_orders_2 @ X2 @ X3 @ X4)
% 0.20/0.65          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (l1_orders_2 @ X2)
% 0.20/0.65          | ~ (v2_lattice3 @ X2)
% 0.20/0.65          | ~ (v5_orders_2 @ X2)
% 0.20/0.65          | (v2_struct_0 @ X2))),
% 0.20/0.65      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.65  thf('65', plain,
% 0.20/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.65         ((v2_struct_0 @ X2)
% 0.20/0.65          | ~ (v5_orders_2 @ X2)
% 0.20/0.65          | ~ (v2_lattice3 @ X2)
% 0.20/0.65          | ~ (l1_orders_2 @ X2)
% 0.20/0.65          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.65          | (r1_orders_2 @ X2 @ (k11_lattice3 @ X2 @ X1 @ X4) @ X4)
% 0.20/0.65          | ~ (m1_subset_1 @ (k11_lattice3 @ X2 @ X1 @ X4) @ (u1_struct_0 @ X2))
% 0.20/0.65          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2)))),
% 0.20/0.66      inference('simplify', [status(thm)], ['64'])).
% 0.20/0.66  thf('66', plain,
% 0.20/0.66      (((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.20/0.66         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 0.20/0.66         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.66         | ~ (l1_orders_2 @ sk_A)
% 0.20/0.66         | ~ (v2_lattice3 @ sk_A)
% 0.20/0.66         | ~ (v5_orders_2 @ sk_A)
% 0.20/0.66         | (v2_struct_0 @ sk_A)))
% 0.20/0.66         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.66      inference('sup-', [status(thm)], ['63', '65'])).
% 0.20/0.66  thf('67', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('69', plain,
% 0.20/0.66      ((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.66         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.66      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.66  thf('70', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('71', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('72', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('73', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('74', plain,
% 0.20/0.66      ((((r1_orders_2 @ sk_A @ sk_D @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.20/0.66         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.66      inference('demod', [status(thm)],
% 0.20/0.66                ['66', '67', '68', '69', '70', '71', '72', '73'])).
% 0.20/0.66  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.66      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.66  thf('76', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_C))
% 0.20/0.66         <= ((((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.66      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.66  thf('77', plain,
% 0.20/0.66      ((~ (r1_orders_2 @ sk_A @ sk_D @ sk_C))
% 0.20/0.66         <= (~ ((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('split', [status(esa)], ['4'])).
% 0.20/0.66  thf('78', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_C)) | 
% 0.20/0.66       ~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.66  thf('79', plain,
% 0.20/0.66      (~ ((r1_orders_2 @ sk_A @ sk_E_1 @ sk_D)) | 
% 0.20/0.66       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) | 
% 0.20/0.66       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_B)) | 
% 0.20/0.66       ~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.66      inference('split', [status(esa)], ['41'])).
% 0.20/0.66  thf('80', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.66        | ((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('81', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_C)) | 
% 0.20/0.66       (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.66      inference('split', [status(esa)], ['80'])).
% 0.20/0.66  thf('82', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.20/0.66      inference('split', [status(esa)], ['0'])).
% 0.20/0.66  thf('83', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_C))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('split', [status(esa)], ['80'])).
% 0.20/0.66  thf('84', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('85', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('86', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('87', plain,
% 0.20/0.66      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ X3 @ X1)
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ X3 @ X4)
% 0.20/0.66          | (r1_orders_2 @ X2 @ (sk_E @ X3 @ X4 @ X1 @ X2) @ X1)
% 0.20/0.66          | ((X3) = (k11_lattice3 @ X2 @ X1 @ X4))
% 0.20/0.66          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (l1_orders_2 @ X2)
% 0.20/0.66          | ~ (v2_lattice3 @ X2)
% 0.20/0.66          | ~ (v5_orders_2 @ X2)
% 0.20/0.66          | (v2_struct_0 @ X2))),
% 0.20/0.66      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.66  thf('88', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((v2_struct_0 @ sk_A)
% 0.20/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.66          | ~ (v2_lattice3 @ sk_A)
% 0.20/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.66  thf('89', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('90', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('92', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((v2_struct_0 @ sk_A)
% 0.20/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.20/0.66  thf('93', plain,
% 0.20/0.66      (![X0 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_C)
% 0.20/0.66          | (r1_orders_2 @ sk_A @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.66          | ((X0) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66          | (v2_struct_0 @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['85', '92'])).
% 0.20/0.66  thf('94', plain,
% 0.20/0.66      (((v2_struct_0 @ sk_A)
% 0.20/0.66        | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66        | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.66        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.66        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.20/0.66      inference('sup-', [status(thm)], ['84', '93'])).
% 0.20/0.66  thf('95', plain,
% 0.20/0.66      (((~ (r1_orders_2 @ sk_A @ sk_D @ sk_B)
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (v2_struct_0 @ sk_A))) <= (((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['83', '94'])).
% 0.20/0.66  thf('96', plain,
% 0.20/0.66      ((((v2_struct_0 @ sk_A)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['82', '95'])).
% 0.20/0.66  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.66      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.66  thf('98', plain,
% 0.20/0.66      ((((r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('clc', [status(thm)], ['96', '97'])).
% 0.20/0.66  thf('99', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_C))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('split', [status(esa)], ['80'])).
% 0.20/0.66  thf('100', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.20/0.66      inference('split', [status(esa)], ['0'])).
% 0.20/0.66  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('102', plain,
% 0.20/0.66      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ X3 @ X1)
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ X3 @ X4)
% 0.20/0.66          | (m1_subset_1 @ (sk_E @ X3 @ X4 @ X1 @ X2) @ (u1_struct_0 @ X2))
% 0.20/0.66          | ((X3) = (k11_lattice3 @ X2 @ X1 @ X4))
% 0.20/0.66          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (l1_orders_2 @ X2)
% 0.20/0.66          | ~ (v2_lattice3 @ X2)
% 0.20/0.66          | ~ (v5_orders_2 @ X2)
% 0.20/0.66          | (v2_struct_0 @ X2))),
% 0.20/0.66      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.66  thf('103', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((v2_struct_0 @ sk_A)
% 0.20/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.66          | ~ (v2_lattice3 @ sk_A)
% 0.20/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66          | (m1_subset_1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.66             (u1_struct_0 @ sk_A))
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.66  thf('104', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('105', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('106', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('107', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((v2_struct_0 @ sk_A)
% 0.20/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66          | (m1_subset_1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.66             (u1_struct_0 @ sk_A))
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.20/0.66  thf('108', plain,
% 0.20/0.66      ((![X0 : $i]:
% 0.20/0.66          (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.20/0.66           | ~ (r1_orders_2 @ sk_A @ sk_D @ X0)
% 0.20/0.66           | (m1_subset_1 @ (sk_E @ sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.66              (u1_struct_0 @ sk_A))
% 0.20/0.66           | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66           | (v2_struct_0 @ sk_A)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['100', '107'])).
% 0.20/0.66  thf('109', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('110', plain,
% 0.20/0.66      ((![X0 : $i]:
% 0.20/0.66          (~ (r1_orders_2 @ sk_A @ sk_D @ X0)
% 0.20/0.66           | (m1_subset_1 @ (sk_E @ sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.66              (u1_struct_0 @ sk_A))
% 0.20/0.66           | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66           | (v2_struct_0 @ sk_A)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.20/0.66      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.66  thf('111', plain,
% 0.20/0.66      ((((v2_struct_0 @ sk_A)
% 0.20/0.66         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.66            (u1_struct_0 @ sk_A))))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['99', '110'])).
% 0.20/0.66  thf('112', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('113', plain,
% 0.20/0.66      ((((v2_struct_0 @ sk_A)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.66            (u1_struct_0 @ sk_A))))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('demod', [status(thm)], ['111', '112'])).
% 0.20/0.66  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.66      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.66  thf('115', plain,
% 0.20/0.66      ((((m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.66          (u1_struct_0 @ sk_A))
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('clc', [status(thm)], ['113', '114'])).
% 0.20/0.66  thf('116', plain,
% 0.20/0.66      ((![X9 : $i]:
% 0.20/0.66          (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66           | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66           | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66           | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B)))
% 0.20/0.66         <= ((![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('split', [status(esa)], ['2'])).
% 0.20/0.66  thf('117', plain,
% 0.20/0.66      (((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | ~ (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.66         | ~ (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.66  thf('118', plain,
% 0.20/0.66      (((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.66         | ~ (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('sup-', [status(thm)], ['98', '117'])).
% 0.20/0.66  thf('119', plain,
% 0.20/0.66      (((~ (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('simplify', [status(thm)], ['118'])).
% 0.20/0.66  thf('120', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.20/0.66      inference('split', [status(esa)], ['0'])).
% 0.20/0.66  thf('121', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_C))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('split', [status(esa)], ['80'])).
% 0.20/0.66  thf('122', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('123', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('124', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('125', plain,
% 0.20/0.66      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ X3 @ X1)
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ X3 @ X4)
% 0.20/0.66          | (r1_orders_2 @ X2 @ (sk_E @ X3 @ X4 @ X1 @ X2) @ X4)
% 0.20/0.66          | ((X3) = (k11_lattice3 @ X2 @ X1 @ X4))
% 0.20/0.66          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (l1_orders_2 @ X2)
% 0.20/0.66          | ~ (v2_lattice3 @ X2)
% 0.20/0.66          | ~ (v5_orders_2 @ X2)
% 0.20/0.66          | (v2_struct_0 @ X2))),
% 0.20/0.66      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.66  thf('126', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((v2_struct_0 @ sk_A)
% 0.20/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.66          | ~ (v2_lattice3 @ sk_A)
% 0.20/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['124', '125'])).
% 0.20/0.66  thf('127', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('128', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('129', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('130', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((v2_struct_0 @ sk_A)
% 0.20/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.20/0.66  thf('131', plain,
% 0.20/0.66      (![X0 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_C)
% 0.20/0.66          | (r1_orders_2 @ sk_A @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.66          | ((X0) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66          | (v2_struct_0 @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['123', '130'])).
% 0.20/0.66  thf('132', plain,
% 0.20/0.66      (((v2_struct_0 @ sk_A)
% 0.20/0.66        | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66        | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.66        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.66        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.20/0.66      inference('sup-', [status(thm)], ['122', '131'])).
% 0.20/0.66  thf('133', plain,
% 0.20/0.66      (((~ (r1_orders_2 @ sk_A @ sk_D @ sk_B)
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (v2_struct_0 @ sk_A))) <= (((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['121', '132'])).
% 0.20/0.66  thf('134', plain,
% 0.20/0.66      ((((v2_struct_0 @ sk_A)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['120', '133'])).
% 0.20/0.66  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.66      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.66  thf('136', plain,
% 0.20/0.66      ((((r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('clc', [status(thm)], ['134', '135'])).
% 0.20/0.66  thf('137', plain,
% 0.20/0.66      (((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (r1_orders_2 @ sk_A @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('clc', [status(thm)], ['119', '136'])).
% 0.20/0.66  thf('138', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('139', plain,
% 0.20/0.66      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ X3 @ X1)
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ X3 @ X4)
% 0.20/0.66          | ~ (r1_orders_2 @ X2 @ (sk_E @ X3 @ X4 @ X1 @ X2) @ X3)
% 0.20/0.66          | ((X3) = (k11_lattice3 @ X2 @ X1 @ X4))
% 0.20/0.66          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.66          | ~ (l1_orders_2 @ X2)
% 0.20/0.66          | ~ (v2_lattice3 @ X2)
% 0.20/0.66          | ~ (v5_orders_2 @ X2)
% 0.20/0.66          | (v2_struct_0 @ X2))),
% 0.20/0.66      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.66  thf('140', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((v2_struct_0 @ sk_A)
% 0.20/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.66          | ~ (v2_lattice3 @ sk_A)
% 0.20/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['138', '139'])).
% 0.20/0.66  thf('141', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('142', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('143', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('144', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((v2_struct_0 @ sk_A)
% 0.20/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.20/0.66  thf('145', plain,
% 0.20/0.66      (((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.20/0.66         | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_B)
% 0.20/0.66         | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.66         | (v2_struct_0 @ sk_A)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('sup-', [status(thm)], ['137', '144'])).
% 0.20/0.66  thf('146', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('147', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.20/0.66      inference('split', [status(esa)], ['0'])).
% 0.20/0.66  thf('148', plain,
% 0.20/0.66      (((r1_orders_2 @ sk_A @ sk_D @ sk_C))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_C)))),
% 0.20/0.66      inference('split', [status(esa)], ['80'])).
% 0.20/0.66  thf('149', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('150', plain,
% 0.20/0.66      (((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.66         | (v2_struct_0 @ sk_A)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 0.20/0.66  thf('151', plain,
% 0.20/0.66      ((((v2_struct_0 @ sk_A) | ((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('simplify', [status(thm)], ['150'])).
% 0.20/0.66  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.66      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.66  thf('153', plain,
% 0.20/0.66      ((((sk_D) = (k11_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.66         <= (((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('clc', [status(thm)], ['151', '152'])).
% 0.20/0.66  thf('154', plain,
% 0.20/0.66      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.66         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.66      inference('sup-', [status(thm)], ['10', '17'])).
% 0.20/0.66  thf('155', plain,
% 0.20/0.66      ((((sk_D) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.66         <= (~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.66      inference('split', [status(esa)], ['4'])).
% 0.20/0.66  thf('156', plain,
% 0.20/0.66      ((((sk_D) != (k11_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.66         <= (~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.66      inference('sup-', [status(thm)], ['154', '155'])).
% 0.20/0.66  thf('157', plain,
% 0.20/0.66      ((((sk_D) != (sk_D)))
% 0.20/0.66         <= (~ (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_B)) & 
% 0.20/0.66             ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) & 
% 0.20/0.66             (![X9 : $i]:
% 0.20/0.66                (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66                 | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66                 | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))))),
% 0.20/0.66      inference('sup-', [status(thm)], ['153', '156'])).
% 0.20/0.66  thf('158', plain,
% 0.20/0.66      (~ ((r1_orders_2 @ sk_A @ sk_D @ sk_C)) | 
% 0.20/0.66       ~
% 0.20/0.66       (![X9 : $i]:
% 0.20/0.66          (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ sk_A))
% 0.20/0.66           | (r1_orders_2 @ sk_A @ X9 @ sk_D)
% 0.20/0.66           | ~ (r1_orders_2 @ sk_A @ X9 @ sk_C)
% 0.20/0.66           | ~ (r1_orders_2 @ sk_A @ X9 @ sk_B))) | 
% 0.20/0.66       ~ ((r1_orders_2 @ sk_A @ sk_D @ sk_B)) | 
% 0.20/0.66       (((sk_D) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.66      inference('simplify', [status(thm)], ['157'])).
% 0.20/0.66  thf('159', plain, ($false),
% 0.20/0.66      inference('sat_resolution*', [status(thm)],
% 0.20/0.66                ['1', '3', '43', '44', '45', '46', '62', '78', '79', '81', 
% 0.20/0.66                 '158'])).
% 0.20/0.66  
% 0.20/0.66  % SZS output end Refutation
% 0.20/0.66  
% 0.20/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
