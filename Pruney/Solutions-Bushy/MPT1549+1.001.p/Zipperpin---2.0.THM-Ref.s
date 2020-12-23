%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1549+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MpcsvuqE4G

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 (1807 expanded)
%              Number of leaves         :   26 ( 502 expanded)
%              Depth                    :   27
%              Number of atoms          : 1864 (28473 expanded)
%              Number of equality atoms :   84 (2396 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(t27_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( r2_yellow_0 @ A @ C )
               => ( ( k2_yellow_0 @ A @ C )
                  = ( k2_yellow_0 @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( l1_orders_2 @ B )
           => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
             => ! [C: $i] :
                  ( ( r2_yellow_0 @ A @ C )
                 => ( ( k2_yellow_0 @ A @ C )
                    = ( k2_yellow_0 @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_yellow_0])).

thf('0',plain,(
    r2_yellow_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(d10_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_yellow_0 @ A @ B )
           => ( ( C
                = ( k2_yellow_0 @ A @ B ) )
            <=> ( ( r1_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
       != ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( g1_orders_2 @ X9 @ X10 )
       != ( g1_orders_2 @ X7 @ X8 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_A )
        = X0 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_A )
        = X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( g1_orders_2 @ X9 @ X10 )
       != ( g1_orders_2 @ X7 @ X8 ) )
      | ( X9 = X7 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_A )
        = X1 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('23',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_A )
        = X1 ) ) ),
    inference(demod,[status(thm)],['20','23','24'])).

thf('26',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

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

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_lattice3 @ X23 @ X24 @ X25 )
      | ( r1_lattice3 @ X21 @ X24 @ X22 )
      | ( X25 != X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X23 ) @ ( u1_orders_2 @ X23 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X21 ) @ ( u1_orders_2 @ X21 ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow_0])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X23 ) @ ( u1_orders_2 @ X23 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X21 ) @ ( u1_orders_2 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r1_lattice3 @ X21 @ X24 @ X22 )
      | ~ ( r1_lattice3 @ X23 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ sk_A @ X2 @ X1 )
      | ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ sk_A @ X2 @ X1 )
      | ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_B @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    r1_lattice3 @ sk_B @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['8','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_lattice3 @ X0 @ X1 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( X2
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( r2_yellow_0 @ sk_B @ X1 )
      | ( ( k2_yellow_0 @ sk_A @ X0 )
        = ( k2_yellow_0 @ sk_B @ X1 ) )
      | ( r1_lattice3 @ sk_B @ X1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ X0 ) @ X1 @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_B @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ sk_B @ X1 )
      | ( ( k2_yellow_0 @ sk_A @ X0 )
        = ( k2_yellow_0 @ sk_B @ X1 ) )
      | ( r1_lattice3 @ sk_B @ X1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ X0 ) @ X1 @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_B @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_B @ sk_C ) )
    | ~ ( r2_yellow_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    r2_yellow_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( ( r2_yellow_0 @ A @ C )
                 => ( r2_yellow_0 @ B @ C ) )
                & ( ( r1_yellow_0 @ A @ C )
                 => ( r1_yellow_0 @ B @ C ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( r2_yellow_0 @ X12 @ X14 )
      | ( r2_yellow_0 @ X11 @ X14 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X12 ) @ ( u1_orders_2 @ X12 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( u1_orders_2 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( r2_yellow_0 @ sk_A @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( r2_yellow_0 @ sk_A @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( r2_yellow_0 @ sk_B @ X0 ) ) ),
    inference(eq_res,[status(thm)],['56'])).

thf('58',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( r2_yellow_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r2_yellow_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','60'])).

thf('62',plain,(
    ( k2_yellow_0 @ sk_A @ sk_C )
 != ( k2_yellow_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_lattice3 @ sk_B @ sk_C @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_lattice3 @ sk_B @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['8','43'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( X2
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( r2_yellow_0 @ sk_B @ X1 )
      | ( ( k2_yellow_0 @ sk_A @ X0 )
        = ( k2_yellow_0 @ sk_B @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ X0 ) @ X1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_B @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ sk_B @ X1 )
      | ( ( k2_yellow_0 @ sk_A @ X0 )
        = ( k2_yellow_0 @ sk_B @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ X0 ) @ X1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_B @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_B @ sk_C ) )
    | ~ ( r2_yellow_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    r2_yellow_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['51','59'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ( k2_yellow_0 @ sk_A @ sk_C )
 != ( k2_yellow_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X23 ) @ ( u1_orders_2 @ X23 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X21 ) @ ( u1_orders_2 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r1_lattice3 @ X21 @ X24 @ X22 )
      | ~ ( r1_lattice3 @ X23 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattice3 @ sk_A @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattice3 @ sk_A @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(eq_res,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_B @ X0 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','85'])).

thf('87',plain,(
    r1_lattice3 @ sk_A @ sk_C @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['63','86'])).

thf('88',plain,(
    m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
       != ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X3 )
      | ( r1_orders_2 @ X0 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X3 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['87','97'])).

thf('99',plain,(
    r2_yellow_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf(t1_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( ( C = E )
                                & ( D = F ) )
                             => ( ( ( r1_orders_2 @ A @ C @ D )
                                 => ( r1_orders_2 @ B @ E @ F ) )
                                & ( ( r2_orders_2 @ A @ C @ D )
                                 => ( r2_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) )).

thf('103',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X17 @ X19 @ X16 )
      | ( r1_orders_2 @ X15 @ X20 @ X18 )
      | ( X16 != X18 )
      | ( X19 != X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X17 ) @ ( u1_orders_2 @ X17 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_yellow_0])).

thf('104',plain,(
    ! [X15: $i,X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X17 ) @ ( u1_orders_2 @ X17 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X20 @ X18 )
      | ~ ( r1_orders_2 @ X17 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X2 @ X1 )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('107',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X2 @ X1 )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','114'])).

thf('116',plain,
    ( ( r1_orders_2 @ sk_B @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','115'])).

thf('117',plain,(
    m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('118',plain,(
    r1_orders_2 @ sk_B @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_C @ sk_B ) @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('120',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ~ ( r2_yellow_0 @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_B @ sk_C ) )
    | ~ ( r1_lattice3 @ sk_B @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    r2_yellow_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['51','59'])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('124',plain,(
    r1_lattice3 @ sk_B @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['8','43'])).

thf('125',plain,
    ( ( k2_yellow_0 @ sk_A @ sk_C )
    = ( k2_yellow_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    ( k2_yellow_0 @ sk_A @ sk_C )
 != ( k2_yellow_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['125','126'])).


%------------------------------------------------------------------------------
