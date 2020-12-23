%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1552+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n6uPovLdsH

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:46 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  131 (1231 expanded)
%              Number of leaves         :   17 ( 303 expanded)
%              Depth                    :   22
%              Number of atoms          : 1605 (38990 expanded)
%              Number of equality atoms :   58 (1476 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(t30_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) )
               => ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ( ( r2_lattice3 @ A @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ( ( r2_lattice3 @ A @ C @ D )
                         => ( r1_orders_2 @ A @ B @ D ) ) ) )
                 => ( ( B
                      = ( k1_yellow_0 @ A @ C ) )
                    & ( r1_yellow_0 @ A @ C ) ) )
                & ( ( ( B
                      = ( k1_yellow_0 @ A @ C ) )
                    & ( r1_yellow_0 @ A @ C ) )
                 => ( ( r2_lattice3 @ A @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ( ( r2_lattice3 @ A @ C @ D )
                         => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_yellow_0])).

thf('0',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
      | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
        | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
      | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 )
      | ( r1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C_1 )
   <= ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
       != ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C_1 @ ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
   <= ( ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['9'])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C_1 )
   <= ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('27',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
       != ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X3 )
      | ( r1_orders_2 @ X0 @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X3 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X0 )
        | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_C_1 ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      & ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_2 )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      & ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 )
      & ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['7'])).

thf('39',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C_1 )
   <= ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('41',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( X2
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
      | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 )
      | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      | ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
        | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) )
   <= ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
        | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
          | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C_1 )
   <= ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('54',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['41'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( X2
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C_1 @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ( r2_lattice3 @ sk_A @ sk_C_1 @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
          | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ) ),
    inference(clc,[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_orders_2 @ X0 @ X2 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( X2
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('64',plain,
    ( ( ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
          | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C_1 )
   <= ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['41'])).

thf('69',plain,
    ( ( ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
          | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
          | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( sk_B
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
      & ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
      & ( r1_yellow_0 @ sk_A @ sk_C_1 )
      & ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
          | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ~ ! [X9: $i] :
          ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
          | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','5','6','8','10','23','39','73'])).

thf('75',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','74'])).

thf('76',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['41'])).

thf('77',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('78',plain,(
    r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','5','6','8','10','23','39','73','77'])).

thf('79',plain,(
    r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ C @ D ) ) )
              & ( r2_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('81',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X4 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','74'])).

thf('88',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
        | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) )
   <= ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
        | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ),
    inference(split,[status(esa)],['50'])).

thf('90',plain,
    ( ! [X9: $i] :
        ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
        | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) )
    | ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('91',plain,(
    ! [X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
      | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','5','6','8','10','23','39','73','90'])).

thf('92',plain,(
    ! [X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X9 )
      | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ X9 ) ) ),
    inference(simpl_trail,[status(thm)],['89','91'])).

thf('93',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ ( sk_D_1 @ sk_B @ sk_C_1 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('94',plain,(
    r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_lattice3 @ X6 @ X5 @ ( sk_D_1 @ X4 @ X5 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ ( sk_D_1 @ sk_B @ sk_C_1 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','74'])).

thf('103',plain,(
    r2_lattice3 @ sk_A @ sk_C_1 @ ( sk_D_1 @ sk_B @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['93','103'])).

thf('105',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_orders_2 @ X6 @ X4 @ ( sk_D_1 @ X4 @ X5 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('106',plain,
    ( ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r2_lattice3 @ sk_A @ sk_C_1 @ sk_B ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('111',plain,(
    r1_yellow_0 @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['75','111'])).


%------------------------------------------------------------------------------
