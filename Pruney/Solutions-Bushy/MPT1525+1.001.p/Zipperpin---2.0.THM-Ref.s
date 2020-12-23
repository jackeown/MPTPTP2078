%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1525+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BQuBybxcfb

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  145 (1456 expanded)
%              Number of leaves         :   23 ( 408 expanded)
%              Depth                    :   35
%              Number of atoms          : 1600 (20466 expanded)
%              Number of equality atoms :   57 (1436 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(d12_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_lattice3 @ A )
      <=> ! [B: $i] :
          ? [C: $i] :
            ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_lattice3 @ A @ B @ D )
                 => ( r1_orders_2 @ A @ C @ D ) ) )
            & ( r2_lattice3 @ A @ B @ C )
            & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v3_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v3_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v3_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v3_lattice3 @ X1 )
      | ( r2_lattice3 @ X1 @ X2 @ ( sk_C @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v3_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf(t3_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
              & ( v3_lattice3 @ A ) )
           => ( v3_lattice3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( l1_orders_2 @ B )
           => ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                  = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
                & ( v3_lattice3 @ A ) )
             => ( v3_lattice3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_yellow_0])).

thf('5',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
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

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B_1 )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['11'])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('14',plain,
    ( ( m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B_1 )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['11'])).

thf('21',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B_1 )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

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

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_lattice3 @ X17 @ X18 @ X19 )
      | ( r2_lattice3 @ X15 @ X18 @ X16 )
      | ( X19 != X16 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X17 ) @ ( u1_orders_2 @ X17 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow_0])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X17 ) @ ( u1_orders_2 @ X17 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r2_lattice3 @ X15 @ X18 @ X16 )
      | ~ ( r2_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B_1 ) ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ X1 )
      | ( r2_lattice3 @ sk_B_1 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['11'])).

thf('28',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ X1 )
      | ( r2_lattice3 @ sk_B_1 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(eq_res,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X1 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X1 @ ( sk_B @ X1 ) @ ( sk_D @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X1 @ ( sk_B @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( v3_lattice3 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v3_lattice3 @ sk_B_1 )
      | ~ ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ X0 )
      | ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_lattice3 @ sk_B_1 )
      | ~ ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ X0 )
      | ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ~ ( v3_lattice3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v3_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_lattice3 @ X1 @ ( sk_B @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( v3_lattice3 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('58',plain,
    ( ~ ( l1_orders_2 @ sk_B_1 )
    | ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('62',plain,
    ( ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ~ ( v3_lattice3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('70',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X17 ) @ ( u1_orders_2 @ X17 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r2_lattice3 @ X15 @ X18 @ X16 )
      | ~ ( r2_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B_1 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ sk_B_1 @ X2 @ X1 )
      | ( r2_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['11'])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('74',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ sk_B_1 @ X2 @ X1 )
      | ( r2_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','80'])).

thf('82',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('83',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_lattice3 @ X1 )
      | ~ ( r2_lattice3 @ X1 @ X2 @ X3 )
      | ( r1_orders_2 @ X1 @ ( sk_C @ X2 @ X1 ) @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( v3_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    r1_orders_2 @ sk_A @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('90',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

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

thf('91',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_orders_2 @ X11 @ X13 @ X10 )
      | ( r1_orders_2 @ X9 @ X14 @ X12 )
      | ( X10 != X12 )
      | ( X13 != X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( u1_orders_2 @ X11 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_yellow_0])).

thf('92',plain,(
    ! [X9: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( u1_orders_2 @ X11 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X9 ) )
      | ( r1_orders_2 @ X9 @ X14 @ X12 )
      | ~ ( r1_orders_2 @ X11 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B_1 ) ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ( r1_orders_2 @ sk_B_1 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['11'])).

thf('95',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ( r1_orders_2 @ sk_B_1 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(eq_res,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['89','102'])).

thf('104',plain,
    ( ( r1_orders_2 @ sk_B_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','103'])).

thf('105',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ( r1_orders_2 @ sk_B_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','104'])).

thf('106',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r1_orders_2 @ sk_B_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_orders_2 @ X1 @ X0 @ ( sk_D @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X1 @ ( sk_B @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( v3_lattice3 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('110',plain,
    ( ~ ( l1_orders_2 @ sk_B_1 )
    | ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('113',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('114',plain,
    ( ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,(
    ~ ( v3_lattice3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['117','118','119'])).


%------------------------------------------------------------------------------
