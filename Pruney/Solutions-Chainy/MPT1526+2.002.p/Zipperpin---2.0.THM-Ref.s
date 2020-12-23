%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G3HoEEeUdP

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:39 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 498 expanded)
%              Number of leaves         :   18 ( 139 expanded)
%              Depth                    :   22
%              Number of atoms          : 1183 (9502 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t4_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
               => ! [D: $i] :
                    ( ( ( r2_lattice3 @ A @ D @ B )
                     => ( r2_lattice3 @ A @ D @ C ) )
                    & ( ( r1_lattice3 @ A @ D @ C )
                     => ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_orders_2 @ A @ B @ C )
                 => ! [D: $i] :
                      ( ( ( r2_lattice3 @ A @ D @ B )
                       => ( r2_lattice3 @ A @ D @ C ) )
                      & ( ( r1_lattice3 @ A @ D @ C )
                       => ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_yellow_0])).

thf('0',plain,
    ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B )
    | ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X10 @ X9 ) @ X10 )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X8 @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_orders_2 @ X9 @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ sk_B ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','22'])).

thf('24',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
   <= ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('27',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C )
   <= ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(split,[status(esa)],['27'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_orders_2 @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X3 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ X4 @ ( sk_D @ X4 @ X6 @ X5 ) )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['47','65'])).

thf('67',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
   <= ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','66'])).

thf('68',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('69',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['26','28','69'])).

thf('71',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['25','70'])).

thf('72',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ sk_B )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(clc,[status(thm)],['23','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X3 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ X0 )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ X0 )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','81'])).

thf('83',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['25','70'])).

thf('86',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ sk_C )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_orders_2 @ X9 @ ( sk_D_1 @ X8 @ X10 @ X9 ) @ X8 )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['25','70'])).

thf('94',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
    | ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('96',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','94','95','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G3HoEEeUdP
% 0.16/0.39  % Computer   : n007.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 18:13:36 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.40  % Python version: Python 3.6.8
% 0.16/0.40  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 208 iterations in 0.152s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.47/0.66  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.66  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.47/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.66  thf(t4_yellow_0, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66               ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.47/0.66                 ( ![D:$i]:
% 0.47/0.66                   ( ( ( r2_lattice3 @ A @ D @ B ) =>
% 0.47/0.66                       ( r2_lattice3 @ A @ D @ C ) ) & 
% 0.47/0.66                     ( ( r1_lattice3 @ A @ D @ C ) =>
% 0.47/0.66                       ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.66          ( ![B:$i]:
% 0.47/0.66            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66              ( ![C:$i]:
% 0.47/0.66                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66                  ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.47/0.66                    ( ![D:$i]:
% 0.47/0.66                      ( ( ( r2_lattice3 @ A @ D @ B ) =>
% 0.47/0.66                          ( r2_lattice3 @ A @ D @ C ) ) & 
% 0.47/0.66                        ( ( r1_lattice3 @ A @ D @ C ) =>
% 0.47/0.66                          ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t4_yellow_0])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)
% 0.47/0.66        | (r1_lattice3 @ sk_A @ sk_D_2 @ sk_C))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (((r1_lattice3 @ sk_A @ sk_D_2 @ sk_C)) | 
% 0.47/0.66       ((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)
% 0.47/0.66        | ~ (r1_lattice3 @ sk_A @ sk_D_2 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['3'])).
% 0.47/0.66  thf('5', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d9_lattice3, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_orders_2 @ A ) =>
% 0.47/0.66       ( ![B:$i,C:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.47/0.66             ( ![D:$i]:
% 0.47/0.66               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.47/0.66          | (r2_hidden @ (sk_D_1 @ X8 @ X10 @ X9) @ X10)
% 0.47/0.66          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.47/0.66          | ~ (l1_orders_2 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | (r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.66  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.66  thf('10', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.47/0.66          | (m1_subset_1 @ (sk_D_1 @ X8 @ X10 @ X9) @ (u1_struct_0 @ X9))
% 0.47/0.66          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.47/0.66          | ~ (l1_orders_2 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | (r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.66  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.47/0.66          | ~ (r2_lattice3 @ X9 @ X10 @ X8)
% 0.47/0.66          | ~ (r2_hidden @ X11 @ X10)
% 0.47/0.66          | (r1_orders_2 @ X9 @ X11 @ X8)
% 0.47/0.66          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.47/0.66          | ~ (l1_orders_2 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B)
% 0.47/0.66          | ~ (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ X1)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['14', '19'])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ sk_B)
% 0.47/0.66          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | (r2_lattice3 @ sk_A @ X0 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '20'])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ sk_B)
% 0.47/0.66          | (r2_lattice3 @ sk_A @ X0 @ sk_C))),
% 0.47/0.66      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      ((((r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)
% 0.47/0.66         | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ sk_D_2 @ sk_A) @ sk_B)))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['4', '22'])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      ((~ (r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)
% 0.47/0.66        | ~ (r1_lattice3 @ sk_A @ sk_D_2 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      ((~ (r2_lattice3 @ sk_A @ sk_D_2 @ sk_C))
% 0.47/0.66         <= (~ ((r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)))),
% 0.47/0.66      inference('split', [status(esa)], ['24'])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (~ ((r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)) | 
% 0.47/0.66       ~ ((r1_lattice3 @ sk_A @ sk_D_2 @ sk_B))),
% 0.47/0.66      inference('split', [status(esa)], ['24'])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      ((~ (r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)
% 0.47/0.66        | (r1_lattice3 @ sk_A @ sk_D_2 @ sk_C))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (((r1_lattice3 @ sk_A @ sk_D_2 @ sk_C)) | 
% 0.47/0.66       ~ ((r2_lattice3 @ sk_A @ sk_D_2 @ sk_C))),
% 0.47/0.66      inference('split', [status(esa)], ['27'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (((r1_lattice3 @ sk_A @ sk_D_2 @ sk_C))
% 0.47/0.66         <= (((r1_lattice3 @ sk_A @ sk_D_2 @ sk_C)))),
% 0.47/0.66      inference('split', [status(esa)], ['27'])).
% 0.47/0.66  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d8_lattice3, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_orders_2 @ A ) =>
% 0.47/0.66       ( ![B:$i,C:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.47/0.66             ( ![D:$i]:
% 0.47/0.66               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.47/0.66          | (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 0.47/0.66          | (r1_lattice3 @ X5 @ X6 @ X4)
% 0.47/0.66          | ~ (l1_orders_2 @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.47/0.66          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ (u1_struct_0 @ X5))
% 0.47/0.66          | (r1_lattice3 @ X5 @ X6 @ X4)
% 0.47/0.66          | ~ (l1_orders_2 @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.66  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.47/0.66  thf('40', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.47/0.66          | ~ (r1_lattice3 @ X5 @ X6 @ X4)
% 0.47/0.66          | ~ (r2_hidden @ X7 @ X6)
% 0.47/0.66          | (r1_orders_2 @ X5 @ X4 @ X7)
% 0.47/0.66          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.47/0.66          | ~ (l1_orders_2 @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.66  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_C)
% 0.47/0.66          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X1)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['39', '44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_B @ X0 @ sk_A))
% 0.47/0.66          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['34', '45'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r1_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_B @ X0 @ sk_A))
% 0.47/0.66          | (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.47/0.66      inference('simplify', [status(thm)], ['46'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.47/0.66  thf('49', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('50', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t26_orders_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66               ( ![D:$i]:
% 0.47/0.66                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66                   ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.47/0.66                       ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.47/0.66                     ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.47/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.66          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.47/0.66          | ~ (r1_orders_2 @ X1 @ X3 @ X2)
% 0.47/0.66          | ~ (r1_orders_2 @ X1 @ X0 @ X3)
% 0.47/0.66          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.47/0.66          | ~ (l1_orders_2 @ X1)
% 0.47/0.66          | ~ (v4_orders_2 @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [t26_orders_2])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v4_orders_2 @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.66  thf('53', plain, ((v4_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['49', '55'])).
% 0.47/0.66  thf('57', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['56', '57'])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_B @ X0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['48', '58'])).
% 0.47/0.66  thf('60', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('61', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.47/0.66          | ~ (r1_orders_2 @ X5 @ X4 @ (sk_D @ X4 @ X6 @ X5))
% 0.47/0.66          | (r1_lattice3 @ X5 @ X6 @ X4)
% 0.47/0.66          | ~ (l1_orders_2 @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.66  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['62', '63'])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r1_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_B @ X0 @ sk_A))
% 0.47/0.66          | (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.47/0.66      inference('clc', [status(thm)], ['59', '64'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_lattice3 @ sk_A @ X0 @ sk_B) | ~ (r1_lattice3 @ sk_A @ X0 @ sk_C))),
% 0.47/0.66      inference('clc', [status(thm)], ['47', '65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      (((r1_lattice3 @ sk_A @ sk_D_2 @ sk_B))
% 0.47/0.66         <= (((r1_lattice3 @ sk_A @ sk_D_2 @ sk_C)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['29', '66'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      ((~ (r1_lattice3 @ sk_A @ sk_D_2 @ sk_B))
% 0.47/0.66         <= (~ ((r1_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['24'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      (((r1_lattice3 @ sk_A @ sk_D_2 @ sk_B)) | 
% 0.47/0.66       ~ ((r1_lattice3 @ sk_A @ sk_D_2 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('70', plain, (~ ((r2_lattice3 @ sk_A @ sk_D_2 @ sk_C))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['26', '28', '69'])).
% 0.47/0.66  thf('71', plain, (~ (r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['25', '70'])).
% 0.47/0.66  thf('72', plain,
% 0.47/0.66      (((r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ sk_D_2 @ sk_A) @ sk_B))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('clc', [status(thm)], ['23', '71'])).
% 0.47/0.66  thf('73', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf('74', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.47/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.66          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.47/0.66          | ~ (r1_orders_2 @ X1 @ X3 @ X2)
% 0.47/0.66          | ~ (r1_orders_2 @ X1 @ X0 @ X3)
% 0.47/0.66          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.47/0.66          | ~ (l1_orders_2 @ X1)
% 0.47/0.66          | ~ (v4_orders_2 @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [t26_orders_2])).
% 0.47/0.66  thf('75', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ X1)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X2)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ X2)
% 0.47/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['73', '74'])).
% 0.47/0.66  thf('76', plain, ((v4_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('78', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ X1)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ X1 @ X2)
% 0.47/0.66          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ X2)
% 0.47/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.47/0.66  thf('79', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66           | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ sk_D_2 @ sk_A) @ X0)
% 0.47/0.66           | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.66           | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.66           | (r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['72', '78'])).
% 0.47/0.66  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('81', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66           | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ sk_D_2 @ sk_A) @ X0)
% 0.47/0.66           | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.66           | (r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['79', '80'])).
% 0.47/0.66  thf('82', plain,
% 0.47/0.66      ((((r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)
% 0.47/0.66         | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.47/0.66         | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ sk_D_2 @ sk_A) @ sk_C)))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '81'])).
% 0.47/0.66  thf('83', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('84', plain,
% 0.47/0.66      ((((r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)
% 0.47/0.66         | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ sk_D_2 @ sk_A) @ sk_C)))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.66  thf('85', plain, (~ (r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['25', '70'])).
% 0.47/0.66  thf('86', plain,
% 0.47/0.66      (((r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ sk_D_2 @ sk_A) @ sk_C))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('clc', [status(thm)], ['84', '85'])).
% 0.47/0.66  thf('87', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('88', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.47/0.66          | ~ (r1_orders_2 @ X9 @ (sk_D_1 @ X8 @ X10 @ X9) @ X8)
% 0.47/0.66          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.47/0.66          | ~ (l1_orders_2 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.47/0.66  thf('89', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | (r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.66  thf('90', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('91', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_lattice3 @ sk_A @ X0 @ sk_C)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_C @ X0 @ sk_A) @ sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['89', '90'])).
% 0.47/0.66  thf('92', plain,
% 0.47/0.66      (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_C))
% 0.47/0.66         <= (((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['86', '91'])).
% 0.47/0.66  thf('93', plain, (~ (r2_lattice3 @ sk_A @ sk_D_2 @ sk_C)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['25', '70'])).
% 0.47/0.66  thf('94', plain, (~ ((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['92', '93'])).
% 0.47/0.66  thf('95', plain,
% 0.47/0.66      (~ ((r1_lattice3 @ sk_A @ sk_D_2 @ sk_B)) | 
% 0.47/0.66       ((r2_lattice3 @ sk_A @ sk_D_2 @ sk_B))),
% 0.47/0.66      inference('split', [status(esa)], ['3'])).
% 0.47/0.66  thf('96', plain, ($false),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['1', '94', '95', '69'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
