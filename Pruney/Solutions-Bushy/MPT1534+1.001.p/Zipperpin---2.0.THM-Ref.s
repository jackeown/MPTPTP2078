%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1534+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tUY7NWpQIT

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 101 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  540 (1476 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t12_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ D @ C ) )
               => ( r1_lattice3 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( ( r1_lattice3 @ A @ B @ C )
                    & ( r1_orders_2 @ A @ D @ C ) )
                 => ( r1_lattice3 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_yellow_0])).

thf('0',plain,(
    ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_1 )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_orders_2 @ A @ B @ C )
                      & ( r1_orders_2 @ A @ C @ D ) )
                   => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r1_orders_2 @ X5 @ X7 @ X6 )
      | ~ ( r1_orders_2 @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    r1_orders_2 @ sk_A @ sk_D_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ ( sk_D @ X0 @ X2 @ X1 ) )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['34','39'])).

thf('41',plain,(
    r1_lattice3 @ sk_A @ sk_B @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).


%------------------------------------------------------------------------------
