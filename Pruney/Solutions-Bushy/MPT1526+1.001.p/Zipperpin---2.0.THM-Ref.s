%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1526+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0zaqW9ewgT

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:43 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 400 expanded)
%              Number of leaves         :   18 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          : 1218 (7610 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ X6 )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_orders_2 @ X5 @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
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

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r1_orders_2 @ X9 @ X8 @ X10 )
      | ~ ( r1_orders_2 @ X9 @ X11 @ X10 )
      | ~ ( r1_orders_2 @ X9 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X2 )
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
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ X0 )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ X0 )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','33'])).

thf('35',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
   <= ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('40',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C )
    | ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C )
   <= ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(split,[status(esa)],['40'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r1_orders_2 @ X9 @ X8 @ X10 )
      | ~ ( r1_orders_2 @ X9 @ X11 @ X10 )
      | ~ ( r1_orders_2 @ X9 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ ( sk_D @ X0 @ X2 @ X1 ) )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
      | ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B ) )
   <= ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','79'])).

thf('81',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
   <= ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('83',plain,
    ( ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['39','41','83'])).

thf('85',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['38','84'])).

thf('86',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ sk_D_2 @ sk_A ) @ sk_C )
   <= ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(clc,[status(thm)],['36','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ X4 )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
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
    inference(simpl_trail,[status(thm)],['38','84'])).

thf('94',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_D_2 @ sk_B )
    | ( r2_lattice3 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('96',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','94','95','83'])).


%------------------------------------------------------------------------------
