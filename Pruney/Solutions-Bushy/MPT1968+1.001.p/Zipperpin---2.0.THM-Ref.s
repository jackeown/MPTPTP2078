%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1968+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C8seYgsrdq

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:37 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  296 (5732 expanded)
%              Number of leaves         :   44 (1532 expanded)
%              Depth                    :   29
%              Number of atoms          : 2907 (175481 expanded)
%              Number of equality atoms :   91 (5346 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t17_waybel_7,conjecture,(
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
                  & ( v1_waybel_0 @ C @ A )
                  & ( v12_waybel_0 @ C @ A )
                  & ( v1_waybel_7 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ~ ( v1_xboole_0 @ C )
                  & ( v1_waybel_0 @ C @ B )
                  & ( v12_waybel_0 @ C @ B )
                  & ( v1_waybel_7 @ C @ B )
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
                    & ( v1_waybel_0 @ C @ A )
                    & ( v12_waybel_0 @ C @ A )
                    & ( v1_waybel_7 @ C @ A )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                 => ( ~ ( v1_xboole_0 @ C )
                    & ( v1_waybel_0 @ C @ B )
                    & ( v12_waybel_0 @ C @ B )
                    & ( v1_waybel_7 @ C @ B )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_waybel_7])).

thf('0',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 )
   <= ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
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
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_orders_2 @ X12 @ X13 )
       != ( g1_orders_2 @ X10 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v12_waybel_0 @ X22 @ X23 )
      | ( v12_waybel_0 @ X21 @ X20 )
      | ( X22 != X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X23 ) @ ( u1_orders_2 @ X23 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X20 ) @ ( u1_orders_2 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_waybel_0])).

thf('12',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X23 ) @ ( u1_orders_2 @ X23 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X20 ) @ ( u1_orders_2 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v12_waybel_0 @ X21 @ X20 )
      | ~ ( v12_waybel_0 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B_1 ) ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( v12_waybel_0 @ X1 @ X0 )
      | ( v12_waybel_0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_orders_2 @ X12 @ X13 )
       != ( g1_orders_2 @ X10 @ X11 ) )
      | ( X13 = X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ) ),
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
      | ~ ( v12_waybel_0 @ X1 @ X0 )
      | ( v12_waybel_0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v12_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v12_waybel_0 @ X0 @ sk_A )
      | ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v12_waybel_0 @ X0 @ sk_A )
      | ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v12_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v12_waybel_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','28'])).

thf('30',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 )
   <= ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_B_1 ),
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

thf(t3_waybel_0,axiom,(
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
                        & ( v1_waybel_0 @ C @ A ) )
                     => ( v1_waybel_0 @ D @ B ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v1_waybel_0 @ X28 @ X27 )
      | ( X29 != X28 )
      | ~ ( v1_waybel_0 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X30 ) @ ( u1_orders_2 @ X30 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X27 ) @ ( u1_orders_2 @ X27 ) ) )
      | ~ ( l1_orders_2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_waybel_0])).

thf('45',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X30 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X30 ) @ ( u1_orders_2 @ X30 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X27 ) @ ( u1_orders_2 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v1_waybel_0 @ X28 @ X30 )
      | ( v1_waybel_0 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B_1 ) ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v1_waybel_0 @ X1 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X1 @ X0 )
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
      | ( v1_waybel_0 @ X1 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_waybel_0 @ X0 @ sk_A )
      | ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(eq_res,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_waybel_0 @ sk_C_2 @ sk_A )
    | ( v1_waybel_0 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','54'])).

thf('56',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
   <= ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,(
    ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['33','38','41','59','60'])).

thf('62',plain,(
    ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(d1_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_waybel_7 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ~ ( ( r2_hidden @ ( k12_lattice3 @ A @ C @ D ) @ B )
                        & ~ ( r2_hidden @ C @ B )
                        & ~ ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_waybel_0 @ X3 @ X4 )
      | ~ ( v12_waybel_0 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( v1_waybel_7 @ X3 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v2_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ X0 )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
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
    v2_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ X0 )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_waybel_7 @ sk_C_2 @ sk_B_1 )
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
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_waybel_0 @ X3 @ X4 )
      | ~ ( v12_waybel_0 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( r2_hidden @ ( k12_lattice3 @ X4 @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X3 )
      | ( v1_waybel_7 @ X3 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v2_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k12_lattice3 @ sk_B_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_D @ X0 @ sk_B_1 ) ) @ X0 )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
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
    v2_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k12_lattice3 @ sk_B_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_D @ X0 @ sk_B_1 ) ) @ X0 )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( r2_hidden @ ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( r2_hidden @ ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ( r2_hidden @ ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('98',plain,(
    r2_hidden @ ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('101',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_waybel_0 @ X3 @ X4 )
      | ~ ( v12_waybel_0 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ( v1_waybel_7 @ X3 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v2_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
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
    v2_lattice3 @ sk_B_1 ),
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
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106','107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','109'])).

thf('111',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('114',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v1_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_waybel_0 @ X3 @ X4 )
      | ~ ( v12_waybel_0 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ( v1_waybel_7 @ X3 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v2_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
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
    v2_lattice3 @ sk_B_1 ),
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
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['119','129'])).

thf('131',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('132',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('134',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('138',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(t21_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v2_lattice3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( r2_yellow_0 @ A @ ( k2_tarski @ B @ C ) ) ) ) ) ) )).

thf('140',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_lattice3 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( r2_yellow_0 @ X17 @ ( k2_tarski @ X19 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_yellow_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_yellow_0 @ sk_B_1 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( v2_lattice3 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('145',plain,(
    v2_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_B_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( r2_yellow_0 @ sk_B_1 @ ( k2_tarski @ X0 @ ( sk_C @ sk_C_2 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','146'])).

thf('148',plain,(
    r2_yellow_0 @ sk_B_1 @ ( k2_tarski @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['118','147'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('149',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_tarski @ X2 @ X1 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('150',plain,(
    r2_yellow_0 @ sk_B_1 @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_yellow_0,axiom,(
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

thf('152',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( ( k2_yellow_0 @ X26 @ X25 )
        = ( k2_yellow_0 @ X24 @ X25 ) )
      | ~ ( r2_yellow_0 @ X26 @ X25 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X26 ) @ ( u1_orders_2 @ X26 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X24 ) @ ( u1_orders_2 @ X24 ) ) )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( r2_yellow_0 @ sk_B_1 @ X1 )
      | ( ( k2_yellow_0 @ sk_B_1 @ X1 )
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( r2_yellow_0 @ sk_B_1 @ X1 )
      | ( ( k2_yellow_0 @ sk_B_1 @ X1 )
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( ( k2_yellow_0 @ sk_B_1 @ X0 )
        = ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_B_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['155'])).

thf('157',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_B_1 @ X0 )
        = ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k2_yellow_0 @ sk_B_1 @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k2_yellow_0 @ sk_A @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['150','158'])).

thf('160',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('161',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf(t40_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k2_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                = ( k12_lattice3 @ A @ B @ C ) ) ) ) ) )).

thf('162',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( ( k2_yellow_0 @ X32 @ ( k7_domain_1 @ ( u1_struct_0 @ X32 ) @ X31 @ X33 ) )
        = ( k12_lattice3 @ X32 @ X31 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t40_yellow_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
        = ( k12_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
        = ( k12_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','168'])).

thf('170',plain,
    ( ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k12_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['160','169'])).

thf('171',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('172',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('173',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k7_domain_1 @ X15 @ X14 @ X16 )
        = ( k2_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 )
        = ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('176',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('177',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('179',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('180',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['177','180'])).

thf('182',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('184',plain,
    ( ~ ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_lattice3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    v2_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['181','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 )
        = ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['174','187'])).

thf('189',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) )
    = ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['171','188'])).

thf('190',plain,
    ( ( k2_yellow_0 @ sk_A @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k12_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['170','189'])).

thf('191',plain,
    ( ( k2_yellow_0 @ sk_B_1 @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k12_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['159','190'])).

thf('192',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('193',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('194',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('195',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( ( k2_yellow_0 @ X32 @ ( k7_domain_1 @ ( u1_struct_0 @ X32 ) @ X31 @ X33 ) )
        = ( k12_lattice3 @ X32 @ X31 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t40_yellow_0])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v2_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k2_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ X0 @ X1 ) )
        = ( k12_lattice3 @ sk_B_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('203',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 ) )
        = ( k12_lattice3 @ sk_B_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['196','197','198','199','200','201','202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
        = ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['193','204'])).

thf('206',plain,
    ( ( k2_yellow_0 @ sk_B_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['192','205'])).

thf('207',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) )
    = ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['171','188'])).

thf('208',plain,
    ( ( k2_yellow_0 @ sk_B_1 @ ( k2_tarski @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) )
    = ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( k12_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) )
    = ( k12_lattice3 @ sk_B_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['191','208'])).

thf('210',plain,(
    r2_hidden @ ( k12_lattice3 @ sk_A @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( sk_D @ sk_C_2 @ sk_B_1 ) ) @ sk_C_2 ),
    inference(demod,[status(thm)],['98','209'])).

thf('211',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_waybel_0 @ X3 @ X4 )
      | ~ ( v12_waybel_0 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v1_waybel_7 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_hidden @ ( k12_lattice3 @ X4 @ X6 @ X5 ) @ X3 )
      | ( r2_hidden @ X5 @ X3 )
      | ( r2_hidden @ X6 @ X3 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r2_hidden @ ( k12_lattice3 @ sk_A @ X0 @ X1 ) @ sk_C_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_waybel_7 @ sk_C_2 @ sk_A )
      | ~ ( v12_waybel_0 @ sk_C_2 @ sk_A )
      | ~ ( v1_waybel_0 @ sk_C_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_waybel_7 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r2_hidden @ ( k12_lattice3 @ sk_A @ X0 @ X1 ) @ sk_C_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218','219','220','221'])).

thf('223',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','222'])).

thf('224',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('225',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('226',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('231',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_waybel_0 @ X3 @ X4 )
      | ~ ( v12_waybel_0 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X4 ) @ X3 )
      | ( v1_waybel_7 @ X3 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v5_orders_2 @ sk_B_1 )
      | ~ ( v2_lattice3 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 ) @ X0 )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v3_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v5_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v2_lattice3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_waybel_7 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 ) @ X0 )
      | ~ ( v12_waybel_0 @ X0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['232','233','234','235','236','237'])).

thf('239',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( v12_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['229','238'])).

thf('240',plain,(
    v12_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('241',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,(
    v1_waybel_0 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('243',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( v1_waybel_7 @ sk_C_2 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,(
    ~ ( v1_waybel_7 @ sk_C_2 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('247',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('248',plain,(
    r2_hidden @ ( sk_C @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ),
    inference(clc,[status(thm)],['228','247'])).

thf('249',plain,(
    v1_waybel_7 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['79','248'])).

thf('250',plain,(
    $false ),
    inference(demod,[status(thm)],['62','249'])).


%------------------------------------------------------------------------------
