%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1970+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.21MbiYxN6E

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  293 (5729 expanded)
%              Number of leaves         :   43 (1531 expanded)
%              Depth                    :   29
%              Number of atoms          : 2884 (175458 expanded)
%              Number of equality atoms :   89 (5344 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v2_waybel_7_type,type,(
    v2_waybel_7: $i > $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(t19_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ( v3_orders_2 @ B )
            & ( v4_orders_2 @ B )
            & ( v5_orders_2 @ B )
            & ( v1_lattice3 @ B )
            & ( v2_lattice3 @ B )
            & ( l1_orders_2 @ B ) )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( v2_waybel_0 @ C @ A )
                  & ( v13_waybel_0 @ C @ A )
                  & ( v2_waybel_7 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ~ ( v1_xboole_0 @ C )
                  & ( v2_waybel_0 @ C @ B )
                  & ( v13_waybel_0 @ C @ B )
                  & ( v2_waybel_7 @ C @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ( v3_orders_2 @ B )
              & ( v4_orders_2 @ B )
              & ( v5_orders_2 @ B )
              & ( v1_lattice3 @ B )
              & ( v2_lattice3 @ B )
              & ( l1_orders_2 @ B ) )
           => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
             => ! [C: $i] :
                  ( ( ~ ( v1_xboole_0 @ C )
                    & ( v2_waybel_0 @ C @ A )
                    & ( v13_waybel_0 @ C @ A )
                    & ( v2_waybel_7 @ C @ A )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                 => ( ~ ( v1_xboole_0 @ C )
                    & ( v2_waybel_0 @ C @ B )
                    & ( v13_waybel_0 @ C @ B )
                    & ( v2_waybel_7 @ C @ B )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_waybel_7])).

thf('0',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 )
   <= ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
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

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( g1_orders_2 @ X10 @ X11 )
       != ( g1_orders_2 @ X8 @ X9 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = X1 )
      | ~ ( l1_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(t25_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( C = D )
                     => ( ( ( v12_waybel_0 @ C @ A )
                         => ( v12_waybel_0 @ D @ B ) )
                        & ( ( v13_waybel_0 @ C @ A )
                         => ( v13_waybel_0 @ D @ B ) ) ) ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ X21 )
      | ( v13_waybel_0 @ X19 @ X18 )
      | ( X20 != X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X21 ) @ ( u1_orders_2 @ X21 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X18 ) @ ( u1_orders_2 @ X18 ) ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_waybel_0])).

thf('12',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X21 ) @ ( u1_orders_2 @ X21 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X18 ) @ ( u1_orders_2 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v13_waybel_0 @ X19 @ X18 )
      | ~ ( v13_waybel_0 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B_1 ) ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( v13_waybel_0 @ X1 @ X0 )
      | ( v13_waybel_0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( g1_orders_2 @ X10 @ X11 )
       != ( g1_orders_2 @ X8 @ X9 ) )
      | ( X11 = X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B_1 )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ X1 @ X0 )
      | ( v13_waybel_0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v13_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v13_waybel_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','28'])).

thf('30',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 )
   <= ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
   <= ( v1_xboole_0 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(t4_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( C = D )
                        & ( v2_waybel_0 @ C @ A ) )
                     => ( v2_waybel_0 @ D @ B ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_waybel_0 @ X29 @ X28 )
      | ( X30 != X29 )
      | ~ ( v2_waybel_0 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X31 ) @ ( u1_orders_2 @ X31 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X28 ) @ ( u1_orders_2 @ X28 ) ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_0])).

thf('45',plain,(
    ! [X28: $i,X29: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X31 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X31 ) @ ( u1_orders_2 @ X31 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X28 ) @ ( u1_orders_2 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_waybel_0 @ X29 @ X31 )
      | ( v2_waybel_0 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B_1 ) ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v2_waybel_0 @ X1 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('48',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_waybel_0 @ X1 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(eq_res,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v2_waybel_0 @ sk_C_2 @ sk_A )
    | ( v2_waybel_0 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','54'])).

thf('56',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
   <= ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,(
    ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['33','38','41','59','60'])).

thf('62',plain,(
    ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(d2_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_waybel_7 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ~ ( ( r2_hidden @ ( k13_lattice3 @ A @ C @ D ) @ B )
                        & ~ ( r2_hidden @ C @ B )
                        & ~ ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v2_waybel_0 @ X1 @ X2 )
      | ~ ( v13_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( v2_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_waybel_7])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v1_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('82',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v2_waybel_0 @ X1 @ X2 )
      | ~ ( v13_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( r2_hidden @ ( k13_lattice3 @ X2 @ ( sk_C @ X1 @ X2 ) @ ( sk_D @ X1 @ X2 ) ) @ X1 )
      | ( v2_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_waybel_7])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v1_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k13_lattice3 @ sk_B_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_D @ X0 @ sk_B_1 ) ) @ X0 )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k13_lattice3 @ sk_B_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_D @ X0 @ sk_B_1 ) ) @ X0 )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( r2_hidden @ ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( r2_hidden @ ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ( r2_hidden @ ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('98',plain,(
    r2_hidden @ ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('101',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v2_waybel_0 @ X1 @ X2 )
      | ~ ( v13_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( v2_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_waybel_7])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v1_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106','107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','109'])).

thf('111',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('114',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('118',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('121',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v2_waybel_0 @ X1 @ X2 )
      | ~ ( v13_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( v2_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_waybel_7])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v1_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['119','129'])).

thf('131',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('132',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('134',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('138',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf(t41_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k1_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                = ( k13_lattice3 @ A @ B @ C ) ) ) ) ) )).

thf('139',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( ( k1_yellow_0 @ X26 @ ( k7_domain_1 @ ( u1_struct_0 @ X26 ) @ X25 @ X27 ) )
        = ( k13_lattice3 @ X26 @ X25 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v1_lattice3 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t41_yellow_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
        = ( k13_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
        = ( k13_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144','145'])).

thf('147',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k13_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['118','146'])).

thf('148',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('149',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('150',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k7_domain_1 @ X13 @ X12 @ X14 )
        = ( k2_tarski @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 )
        = ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('153',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('154',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('156',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('157',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['154','157'])).

thf('159',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('161',plain,
    ( ~ ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_lattice3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v2_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['158','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 )
        = ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['151','164'])).

thf('166',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) )
    = ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['148','165'])).

thf('167',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k13_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['147','166'])).

thf('168',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('169',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('170',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('171',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( ( k1_yellow_0 @ X26 @ ( k7_domain_1 @ ( u1_struct_0 @ X26 ) @ X25 @ X27 ) )
        = ( k13_lattice3 @ X26 @ X25 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v1_lattice3 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t41_yellow_0])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v1_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k1_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ X0 @ X1 ) )
        = ( k13_lattice3 @ sk_B_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('179',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 ) )
        = ( k13_lattice3 @ sk_B_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176','177','178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
        = ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['169','180'])).

thf('182',plain,
    ( ( k1_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['168','181'])).

thf('183',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) )
    = ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['148','165'])).

thf('184',plain,
    ( ( k1_yellow_0 @ sk_B_1 @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('186',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('187',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(t20_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_lattice3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( r1_yellow_0 @ A @ ( k2_tarski @ B @ C ) ) ) ) ) ) )).

thf('188',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_lattice3 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r1_yellow_0 @ X15 @ ( k2_tarski @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t20_yellow_0])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_yellow_0 @ sk_B_1 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( v1_lattice3 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('193',plain,(
    v1_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_B_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_B_1 @ ( k2_tarski @ X0 @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['186','194'])).

thf('196',plain,(
    r1_yellow_0 @ sk_B_1 @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['185','195'])).

thf('197',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( r1_yellow_0 @ A @ C )
               => ( ( k1_yellow_0 @ A @ C )
                  = ( k1_yellow_0 @ B @ C ) ) ) ) ) ) )).

thf('198',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( ( k1_yellow_0 @ X24 @ X23 )
        = ( k1_yellow_0 @ X22 @ X23 ) )
      | ~ ( r1_yellow_0 @ X24 @ X23 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X24 ) @ ( u1_orders_2 @ X24 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X22 ) @ ( u1_orders_2 @ X22 ) ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_0])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( r1_yellow_0 @ sk_B_1 @ X1 )
      | ( ( k1_yellow_0 @ sk_B_1 @ X1 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( r1_yellow_0 @ sk_B_1 @ X1 )
      | ( ( k1_yellow_0 @ sk_B_1 @ X1 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_B_1 @ X0 )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_B_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['201'])).

thf('203',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_B_1 @ X0 )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( k1_yellow_0 @ sk_B_1 @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k1_yellow_0 @ sk_A @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('206',plain,
    ( ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) )
    = ( k1_yellow_0 @ sk_A @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['184','205'])).

thf('207',plain,
    ( ( k13_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) )
    = ( k13_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['167','206'])).

thf('208',plain,(
    r2_hidden @ ( k13_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 ),
    inference(demod,[status(thm)],['98','207'])).

thf('209',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v2_waybel_0 @ X1 @ X2 )
      | ~ ( v13_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v2_waybel_7 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r2_hidden @ ( k13_lattice3 @ X2 @ X4 @ X3 ) @ X1 )
      | ( r2_hidden @ X3 @ X1 )
      | ( r2_hidden @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_waybel_7])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r2_hidden @ ( k13_lattice3 @ sk_A @ X0 @ X1 ) @ sk_C_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_waybel_7 @ sk_C_2 @ sk_A )
      | ~ ( v13_waybel_0 @ sk_C_2 @ sk_A )
      | ~ ( v2_waybel_0 @ sk_C_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_waybel_7 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r2_hidden @ ( k13_lattice3 @ sk_A @ X0 @ X1 ) @ sk_C_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['211','212','213','214','215','216','217','218','219'])).

thf('221',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['208','220'])).

thf('222',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('223',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('224',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('229',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v2_waybel_0 @ X1 @ X2 )
      | ~ ( v13_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X2 ) @ X1 )
      | ( v2_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_waybel_7])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v1_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v1_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_waybel_7 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v2_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['230','231','232','233','234','235'])).

thf('237',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v13_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['227','236'])).

thf('238',plain,(
    v13_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('239',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    v2_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('241',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( v2_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['241','242'])).

thf('244',plain,(
    ~ ( v2_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('245',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,(
    r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ),
    inference(clc,[status(thm)],['226','245'])).

thf('247',plain,(
    v2_waybel_7 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['79','246'])).

thf('248',plain,(
    $false ),
    inference(demod,[status(thm)],['62','247'])).


%------------------------------------------------------------------------------
