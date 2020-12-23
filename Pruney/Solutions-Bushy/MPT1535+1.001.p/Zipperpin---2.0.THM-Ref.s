%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1535+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8G0S1HM4UU

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
% Statistics : Number of formulae       :  114 ( 355 expanded)
%              Number of leaves         :   21 ( 103 expanded)
%              Depth                    :   23
%              Number of atoms          : 1052 (5091 expanded)
%              Number of equality atoms :   35 ( 252 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_yellow_0_type,type,(
    v2_yellow_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(t13_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ( ( ( v1_yellow_0 @ A )
               => ( v1_yellow_0 @ B ) )
              & ( ( v2_yellow_0 @ A )
               => ( v2_yellow_0 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( l1_orders_2 @ B )
           => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
             => ( ( ( v1_yellow_0 @ A )
                 => ( v1_yellow_0 @ B ) )
                & ( ( v2_yellow_0 @ A )
                 => ( v2_yellow_0 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_yellow_0])).

thf('0',plain,
    ( ( v1_yellow_0 @ sk_A )
    | ( v2_yellow_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v2_yellow_0 @ sk_A )
    | ( v1_yellow_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_yellow_0 @ A )
      <=> ? [B: $i] :
            ( ( r1_lattice3 @ A @ ( u1_struct_0 @ A ) @ B )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ( r1_lattice3 @ X0 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('4',plain,
    ( ( v1_yellow_0 @ sk_A )
    | ~ ( v2_yellow_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_yellow_0 @ sk_A )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('7',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_orders_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i,D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ! [E: $i] :
                    ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                   => ( ( D = E )
                     => ( ( ( r2_lattice3 @ A @ C @ D )
                         => ( r2_lattice3 @ B @ C @ E ) )
                        & ( ( r1_lattice3 @ A @ C @ D )
                         => ( r1_lattice3 @ B @ C @ E ) ) ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_lattice3 @ X11 @ X12 @ X13 )
      | ( r1_lattice3 @ X9 @ X12 @ X10 )
      | ( X13 != X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( u1_orders_2 @ X11 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow_0])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( u1_orders_2 @ X11 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r1_lattice3 @ X9 @ X12 @ X10 )
      | ~ ( r1_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattice3 @ sk_B_2 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattice3 @ sk_B_2 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_orders_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_2 )
        = X1 )
      | ~ ( l1_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_2 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattice3 @ sk_B_2 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_B_2 @ X1 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ( r1_lattice3 @ sk_B_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ( r1_lattice3 @ sk_B_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ( r1_lattice3 @ sk_B_2 @ X0 @ ( sk_B @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ sk_A )
      | ( r1_lattice3 @ sk_B_2 @ X0 @ ( sk_B @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_B @ sk_A ) )
        | ( r1_lattice3 @ sk_B_2 @ X0 @ ( sk_B @ sk_A ) ) )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ( r1_lattice3 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_yellow_0 @ sk_A )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('33',plain,
    ( ( r1_lattice3 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ X0 @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ~ ( l1_orders_2 @ sk_B_2 )
      | ( v1_yellow_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ( v1_yellow_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_yellow_0 @ sk_B_2 ) )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ~ ( v1_yellow_0 @ sk_B_2 )
    | ~ ( v2_yellow_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_yellow_0 @ sk_B_2 )
   <= ~ ( v1_yellow_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ~ ( v1_yellow_0 @ sk_B_2 )
    | ~ ( v2_yellow_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['41'])).

thf('44',plain,
    ( ~ ( v1_yellow_0 @ sk_B_2 )
    | ( v2_yellow_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_yellow_0 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['44'])).

thf(d5_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_yellow_0 @ A )
      <=> ? [B: $i] :
            ( ( r2_lattice3 @ A @ ( u1_struct_0 @ A ) @ B )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X2: $i] :
      ( ~ ( v2_yellow_0 @ X2 )
      | ( m1_subset_1 @ ( sk_B_1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf('47',plain,(
    ! [X2: $i] :
      ( ~ ( v2_yellow_0 @ X2 )
      | ( r2_lattice3 @ X2 @ ( u1_struct_0 @ X2 ) @ ( sk_B_1 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf('48',plain,
    ( ( v2_yellow_0 @ sk_A )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('49',plain,(
    ! [X2: $i] :
      ( ~ ( v2_yellow_0 @ X2 )
      | ( m1_subset_1 @ ( sk_B_1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf('50',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_orders_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_lattice3 @ X11 @ X12 @ X13 )
      | ( r2_lattice3 @ X9 @ X12 @ X10 )
      | ( X13 != X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( u1_orders_2 @ X11 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow_0])).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( u1_orders_2 @ X11 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_lattice3 @ X9 @ X12 @ X10 )
      | ~ ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ X1 )
      | ( r2_lattice3 @ sk_B_2 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ X1 )
      | ( r2_lattice3 @ sk_B_2 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_2 @ X1 @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(eq_res,[status(thm)],['55'])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_2 @ X1 @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_2 @ X1 @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ( r2_lattice3 @ sk_B_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_yellow_0 @ sk_A )
      | ( r2_lattice3 @ sk_B_2 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','61'])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v2_yellow_0 @ sk_A )
      | ( r2_lattice3 @ sk_B_2 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_B_1 @ sk_A ) )
        | ( r2_lattice3 @ sk_B_2 @ X0 @ ( sk_B_1 @ sk_A ) ) )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_yellow_0 @ sk_A )
      | ( r2_lattice3 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) ) )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','65'])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_yellow_0 @ sk_A )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('69',plain,
    ( ( r2_lattice3 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ X2 @ ( u1_struct_0 @ X2 ) @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( v2_yellow_0 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ~ ( l1_orders_2 @ sk_B_2 )
      | ( v2_yellow_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ( v2_yellow_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_yellow_0 @ sk_B_2 ) )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_yellow_0 @ sk_A )
      | ( v2_yellow_0 @ sk_B_2 ) )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','76'])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_yellow_0 @ sk_A )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('80',plain,
    ( ( v2_yellow_0 @ sk_B_2 )
   <= ( v2_yellow_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v2_yellow_0 @ sk_B_2 )
   <= ~ ( v2_yellow_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['41'])).

thf('82',plain,
    ( ( v2_yellow_0 @ sk_B_2 )
    | ~ ( v2_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_yellow_0 @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['43','45','82'])).

thf('84',plain,(
    ~ ( v1_yellow_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['42','83'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','84'])).

thf('86',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A ) )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_yellow_0 @ sk_A )
   <= ( v1_yellow_0 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('89',plain,(
    ~ ( v1_yellow_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ~ ( v2_yellow_0 @ sk_B_2 )
    | ( v1_yellow_0 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('91',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','89','90','82'])).


%------------------------------------------------------------------------------
