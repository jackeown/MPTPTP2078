%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1533+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ootBiQfZso

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 105 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  582 (1566 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)

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

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

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

thf(t11_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r2_lattice3 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ D ) )
               => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( ( r2_lattice3 @ A @ B @ C )
                    & ( r1_orders_2 @ A @ C @ D ) )
                 => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_yellow_0])).

thf('0',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ( r2_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( r2_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_orders_2 @ X1 @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_C )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_1 )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('25',plain,(
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

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_1 )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D_1 )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    r1_orders_2 @ sk_A @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_1 )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_D_1 ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ( r2_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r2_lattice3 @ sk_A @ sk_B @ sk_D_1 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).


%------------------------------------------------------------------------------
