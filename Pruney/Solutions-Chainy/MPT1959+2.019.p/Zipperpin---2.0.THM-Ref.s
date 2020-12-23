%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5mOCdeqiPF

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:11 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 619 expanded)
%              Number of leaves         :   38 ( 186 expanded)
%              Depth                    :   30
%              Number of atoms          : 1572 (10630 expanded)
%              Number of equality atoms :   36 (  90 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t8_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
            <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_7])).

thf('0',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( r1_yellow_0 @ X21 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v1_yellow_0 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X3 @ X4 ) @ X4 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k1_yellow_0 @ X15 @ X16 ) )
      | ~ ( r2_lattice3 @ X15 @ X16 @ X18 )
      | ( r1_orders_2 @ X15 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_yellow_0 @ X15 @ X16 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( r1_yellow_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ ( k1_yellow_0 @ X15 @ X16 ) @ X18 )
      | ~ ( r2_lattice3 @ X15 @ X16 @ X18 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X14: $i] :
      ( ( ( k3_yellow_0 @ X14 )
        = ( k1_yellow_0 @ X14 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('33',plain,(
    ! [X21: $i] :
      ( ( r1_yellow_0 @ X21 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v1_yellow_0 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k1_yellow_0 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ X2 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d20_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r1_orders_2 @ X23 @ X25 @ X24 )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','65'])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('81',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','81'])).

thf('83',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('84',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('86',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['90'])).

thf('92',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['89','91'])).

thf('93',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('94',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('96',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_subset_1 @ X27 @ X26 )
      | ( X27 != X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('97',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_subset_1 @ X26 @ X26 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['90'])).

thf('101',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('103',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X14: $i] :
      ( ( ( k3_yellow_0 @ X14 )
        = ( k1_yellow_0 @ X14 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('107',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('110',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['105','111'])).

thf('113',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('114',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['90'])).

thf('119',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','99','100','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5mOCdeqiPF
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:51:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.98/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.98/1.16  % Solved by: fo/fo7.sh
% 0.98/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.16  % done 993 iterations in 0.697s
% 0.98/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.98/1.16  % SZS output start Refutation
% 0.98/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.16  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.98/1.16  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.98/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.16  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.98/1.16  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.98/1.16  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.98/1.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.16  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.98/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.16  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.98/1.16  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.98/1.16  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.98/1.16  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.98/1.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.98/1.16  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.98/1.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.98/1.16  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.98/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.16  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.98/1.16  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.98/1.16  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.98/1.16  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.98/1.16  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.98/1.16  thf(t8_waybel_7, conjecture,
% 0.98/1.16    (![A:$i]:
% 0.98/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.98/1.16         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.98/1.16         ( l1_orders_2 @ A ) ) =>
% 0.98/1.16       ( ![B:$i]:
% 0.98/1.16         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.98/1.16             ( v13_waybel_0 @ B @ A ) & 
% 0.98/1.16             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.16           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.98/1.16             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.98/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.16    (~( ![A:$i]:
% 0.98/1.16        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.98/1.16            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.98/1.16            ( l1_orders_2 @ A ) ) =>
% 0.98/1.16          ( ![B:$i]:
% 0.98/1.16            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.98/1.16                ( v13_waybel_0 @ B @ A ) & 
% 0.98/1.16                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.16              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.98/1.16                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.98/1.16    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.98/1.16  thf('0', plain,
% 0.98/1.16      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.98/1.16        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('1', plain,
% 0.98/1.16      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.98/1.16       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('split', [status(esa)], ['0'])).
% 0.98/1.16  thf(t42_yellow_0, axiom,
% 0.98/1.16    (![A:$i]:
% 0.98/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.98/1.16         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.98/1.16       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.98/1.16         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.98/1.16  thf('2', plain,
% 0.98/1.16      (![X21 : $i]:
% 0.98/1.16         ((r1_yellow_0 @ X21 @ k1_xboole_0)
% 0.98/1.16          | ~ (l1_orders_2 @ X21)
% 0.98/1.16          | ~ (v1_yellow_0 @ X21)
% 0.98/1.16          | ~ (v5_orders_2 @ X21)
% 0.98/1.16          | (v2_struct_0 @ X21))),
% 0.98/1.16      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.98/1.16  thf('3', plain,
% 0.98/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(t49_subset_1, axiom,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.98/1.16         ( ( A ) = ( B ) ) ) ))).
% 0.98/1.16  thf('4', plain,
% 0.98/1.16      (![X3 : $i, X4 : $i]:
% 0.98/1.16         ((m1_subset_1 @ (sk_C @ X3 @ X4) @ X4)
% 0.98/1.16          | ((X4) = (X3))
% 0.98/1.16          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.98/1.16      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.98/1.16  thf('5', plain,
% 0.98/1.16      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.16           (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['3', '4'])).
% 0.98/1.16  thf(d9_lattice3, axiom,
% 0.98/1.16    (![A:$i]:
% 0.98/1.16     ( ( l1_orders_2 @ A ) =>
% 0.98/1.16       ( ![B:$i,C:$i]:
% 0.98/1.16         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.16           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.98/1.16             ( ![D:$i]:
% 0.98/1.16               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.16                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.98/1.16  thf('6', plain,
% 0.98/1.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.98/1.16         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.98/1.16          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 0.98/1.16          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.98/1.16          | ~ (l1_orders_2 @ X11))),
% 0.98/1.16      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.98/1.16  thf('7', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16          | ~ (l1_orders_2 @ sk_A)
% 0.98/1.16          | (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | (r2_hidden @ 
% 0.98/1.16             (sk_D @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_A) @ X0))),
% 0.98/1.16      inference('sup-', [status(thm)], ['5', '6'])).
% 0.98/1.16  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('9', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16          | (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | (r2_hidden @ 
% 0.98/1.16             (sk_D @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_A) @ X0))),
% 0.98/1.16      inference('demod', [status(thm)], ['7', '8'])).
% 0.98/1.16  thf(d1_xboole_0, axiom,
% 0.98/1.16    (![A:$i]:
% 0.98/1.16     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.98/1.16  thf('10', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.98/1.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.98/1.16  thf('11', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         ((r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.16      inference('sup-', [status(thm)], ['9', '10'])).
% 0.98/1.16  thf('12', plain,
% 0.98/1.16      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.16           (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['3', '4'])).
% 0.98/1.16  thf(dt_k1_yellow_0, axiom,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( l1_orders_2 @ A ) =>
% 0.98/1.16       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.98/1.16  thf('13', plain,
% 0.98/1.16      (![X19 : $i, X20 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X19)
% 0.98/1.16          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 0.98/1.16      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.98/1.16  thf(d9_yellow_0, axiom,
% 0.98/1.16    (![A:$i]:
% 0.98/1.16     ( ( l1_orders_2 @ A ) =>
% 0.98/1.16       ( ![B:$i,C:$i]:
% 0.98/1.16         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.16           ( ( r1_yellow_0 @ A @ B ) =>
% 0.98/1.16             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.98/1.16               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.98/1.16                 ( ![D:$i]:
% 0.98/1.16                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.16                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.98/1.16                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.98/1.16  thf('14', plain,
% 0.98/1.16      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.98/1.16         (((X17) != (k1_yellow_0 @ X15 @ X16))
% 0.98/1.16          | ~ (r2_lattice3 @ X15 @ X16 @ X18)
% 0.98/1.16          | (r1_orders_2 @ X15 @ X17 @ X18)
% 0.98/1.16          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.98/1.16          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.98/1.16          | ~ (r1_yellow_0 @ X15 @ X16)
% 0.98/1.16          | ~ (l1_orders_2 @ X15))),
% 0.98/1.16      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.98/1.16  thf('15', plain,
% 0.98/1.16      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X15)
% 0.98/1.16          | ~ (r1_yellow_0 @ X15 @ X16)
% 0.98/1.16          | ~ (m1_subset_1 @ (k1_yellow_0 @ X15 @ X16) @ (u1_struct_0 @ X15))
% 0.98/1.16          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.98/1.16          | (r1_orders_2 @ X15 @ (k1_yellow_0 @ X15 @ X16) @ X18)
% 0.98/1.16          | ~ (r2_lattice3 @ X15 @ X16 @ X18))),
% 0.98/1.16      inference('simplify', [status(thm)], ['14'])).
% 0.98/1.16  thf('16', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X0)
% 0.98/1.16          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.98/1.16          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.98/1.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.98/1.16          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.98/1.16          | ~ (l1_orders_2 @ X0))),
% 0.98/1.16      inference('sup-', [status(thm)], ['13', '15'])).
% 0.98/1.16  thf('17', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (r1_yellow_0 @ X0 @ X1)
% 0.98/1.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.98/1.16          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.98/1.16          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.98/1.16          | ~ (l1_orders_2 @ X0))),
% 0.98/1.16      inference('simplify', [status(thm)], ['16'])).
% 0.98/1.16  thf('18', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16          | ~ (l1_orders_2 @ sk_A)
% 0.98/1.16          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.98/1.16             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.98/1.16      inference('sup-', [status(thm)], ['12', '17'])).
% 0.98/1.16  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('20', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.98/1.16             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.98/1.16      inference('demod', [status(thm)], ['18', '19'])).
% 0.98/1.16  thf('21', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         (~ (v1_xboole_0 @ X0)
% 0.98/1.16          | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.98/1.16          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.98/1.16             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['11', '20'])).
% 0.98/1.16  thf('22', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.98/1.16           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.98/1.16          | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.16      inference('simplify', [status(thm)], ['21'])).
% 0.98/1.16  thf('23', plain,
% 0.98/1.16      (((v2_struct_0 @ sk_A)
% 0.98/1.16        | ~ (v5_orders_2 @ sk_A)
% 0.98/1.16        | ~ (v1_yellow_0 @ sk_A)
% 0.98/1.16        | ~ (l1_orders_2 @ sk_A)
% 0.98/1.16        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.98/1.16        | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.98/1.16           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.16      inference('sup-', [status(thm)], ['2', '22'])).
% 0.98/1.16  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('25', plain, ((v1_yellow_0 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.98/1.16  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.16      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.16  thf('28', plain,
% 0.98/1.16      (((v2_struct_0 @ sk_A)
% 0.98/1.16        | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.98/1.16           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.16      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.98/1.16  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('30', plain,
% 0.98/1.16      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.98/1.16         (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.98/1.16      inference('clc', [status(thm)], ['28', '29'])).
% 0.98/1.16  thf('31', plain,
% 0.98/1.16      (![X19 : $i, X20 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X19)
% 0.98/1.16          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 0.98/1.16      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.98/1.16  thf(d11_yellow_0, axiom,
% 0.98/1.16    (![A:$i]:
% 0.98/1.16     ( ( l1_orders_2 @ A ) =>
% 0.98/1.16       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.98/1.16  thf('32', plain,
% 0.98/1.16      (![X14 : $i]:
% 0.98/1.16         (((k3_yellow_0 @ X14) = (k1_yellow_0 @ X14 @ k1_xboole_0))
% 0.98/1.16          | ~ (l1_orders_2 @ X14))),
% 0.98/1.16      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.98/1.16  thf('33', plain,
% 0.98/1.16      (![X21 : $i]:
% 0.98/1.16         ((r1_yellow_0 @ X21 @ k1_xboole_0)
% 0.98/1.16          | ~ (l1_orders_2 @ X21)
% 0.98/1.16          | ~ (v1_yellow_0 @ X21)
% 0.98/1.16          | ~ (v5_orders_2 @ X21)
% 0.98/1.16          | (v2_struct_0 @ X21))),
% 0.98/1.16      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.98/1.16  thf('34', plain,
% 0.98/1.16      (![X19 : $i, X20 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X19)
% 0.98/1.16          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 0.98/1.16      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.98/1.16  thf('35', plain,
% 0.98/1.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.98/1.16         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.98/1.16          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 0.98/1.16          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.98/1.16          | ~ (l1_orders_2 @ X11))),
% 0.98/1.16      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.98/1.16  thf('36', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X0)
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.98/1.16          | (r2_hidden @ (sk_D @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2))),
% 0.98/1.16      inference('sup-', [status(thm)], ['34', '35'])).
% 0.98/1.16  thf('37', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         ((r2_hidden @ (sk_D @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2)
% 0.98/1.16          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.98/1.16          | ~ (l1_orders_2 @ X0))),
% 0.98/1.16      inference('simplify', [status(thm)], ['36'])).
% 0.98/1.16  thf('38', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.98/1.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.98/1.16  thf('39', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X1)
% 0.98/1.16          | (r2_lattice3 @ X1 @ X0 @ (k1_yellow_0 @ X1 @ X2))
% 0.98/1.16          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.16      inference('sup-', [status(thm)], ['37', '38'])).
% 0.98/1.16  thf('40', plain,
% 0.98/1.16      (![X19 : $i, X20 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X19)
% 0.98/1.16          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 0.98/1.16      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.98/1.16  thf('41', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (r1_yellow_0 @ X0 @ X1)
% 0.98/1.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.98/1.16          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.98/1.16          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.98/1.16          | ~ (l1_orders_2 @ X0))),
% 0.98/1.16      inference('simplify', [status(thm)], ['16'])).
% 0.98/1.16  thf('42', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ X0)
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.98/1.16          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.98/1.16             (k1_yellow_0 @ X0 @ X1))
% 0.98/1.16          | ~ (r1_yellow_0 @ X0 @ X2))),
% 0.98/1.16      inference('sup-', [status(thm)], ['40', '41'])).
% 0.98/1.16  thf('43', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (r1_yellow_0 @ X0 @ X2)
% 0.98/1.16          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.98/1.16             (k1_yellow_0 @ X0 @ X1))
% 0.98/1.16          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.98/1.16          | ~ (l1_orders_2 @ X0))),
% 0.98/1.16      inference('simplify', [status(thm)], ['42'])).
% 0.98/1.16  thf('44', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (v1_xboole_0 @ X2)
% 0.98/1.16          | ~ (l1_orders_2 @ X1)
% 0.98/1.16          | ~ (l1_orders_2 @ X1)
% 0.98/1.16          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 0.98/1.16             (k1_yellow_0 @ X1 @ X0))
% 0.98/1.16          | ~ (r1_yellow_0 @ X1 @ X2))),
% 0.98/1.16      inference('sup-', [status(thm)], ['39', '43'])).
% 0.98/1.16  thf('45', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         (~ (r1_yellow_0 @ X1 @ X2)
% 0.98/1.16          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 0.98/1.16             (k1_yellow_0 @ X1 @ X0))
% 0.98/1.16          | ~ (l1_orders_2 @ X1)
% 0.98/1.16          | ~ (v1_xboole_0 @ X2))),
% 0.98/1.16      inference('simplify', [status(thm)], ['44'])).
% 0.98/1.16  thf('46', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]:
% 0.98/1.16         ((v2_struct_0 @ X0)
% 0.98/1.16          | ~ (v5_orders_2 @ X0)
% 0.98/1.16          | ~ (v1_yellow_0 @ X0)
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.98/1.16             (k1_yellow_0 @ X0 @ X1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['33', '45'])).
% 0.98/1.16  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.16      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.16  thf('48', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]:
% 0.98/1.16         ((v2_struct_0 @ X0)
% 0.98/1.16          | ~ (v5_orders_2 @ X0)
% 0.98/1.16          | ~ (v1_yellow_0 @ X0)
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.98/1.16             (k1_yellow_0 @ X0 @ X1)))),
% 0.98/1.16      inference('demod', [status(thm)], ['46', '47'])).
% 0.98/1.16  thf('49', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]:
% 0.98/1.16         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.98/1.16           (k1_yellow_0 @ X0 @ X1))
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | ~ (v1_yellow_0 @ X0)
% 0.98/1.16          | ~ (v5_orders_2 @ X0)
% 0.98/1.16          | (v2_struct_0 @ X0))),
% 0.98/1.16      inference('simplify', [status(thm)], ['48'])).
% 0.98/1.16  thf('50', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]:
% 0.98/1.16         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | (v2_struct_0 @ X0)
% 0.98/1.16          | ~ (v5_orders_2 @ X0)
% 0.98/1.16          | ~ (v1_yellow_0 @ X0)
% 0.98/1.16          | ~ (l1_orders_2 @ X0))),
% 0.98/1.16      inference('sup+', [status(thm)], ['32', '49'])).
% 0.98/1.16  thf('51', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]:
% 0.98/1.16         (~ (v1_yellow_0 @ X0)
% 0.98/1.16          | ~ (v5_orders_2 @ X0)
% 0.98/1.16          | (v2_struct_0 @ X0)
% 0.98/1.16          | ~ (l1_orders_2 @ X0)
% 0.98/1.16          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 0.98/1.16      inference('simplify', [status(thm)], ['50'])).
% 0.98/1.16  thf('52', plain,
% 0.98/1.16      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('split', [status(esa)], ['0'])).
% 0.98/1.16  thf('53', plain,
% 0.98/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(t4_subset, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i]:
% 0.98/1.16     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.98/1.16       ( m1_subset_1 @ A @ C ) ))).
% 0.98/1.16  thf('54', plain,
% 0.98/1.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.98/1.16         (~ (r2_hidden @ X7 @ X8)
% 0.98/1.16          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.98/1.16          | (m1_subset_1 @ X7 @ X9))),
% 0.98/1.16      inference('cnf', [status(esa)], [t4_subset])).
% 0.98/1.16  thf('55', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.16          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.98/1.16      inference('sup-', [status(thm)], ['53', '54'])).
% 0.98/1.16  thf('56', plain,
% 0.98/1.16      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['52', '55'])).
% 0.98/1.16  thf('57', plain,
% 0.98/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(d20_waybel_0, axiom,
% 0.98/1.16    (![A:$i]:
% 0.98/1.16     ( ( l1_orders_2 @ A ) =>
% 0.98/1.16       ( ![B:$i]:
% 0.98/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.16           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.98/1.16             ( ![C:$i]:
% 0.98/1.16               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.16                 ( ![D:$i]:
% 0.98/1.16                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.16                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.98/1.16                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.98/1.16  thf('58', plain,
% 0.98/1.16      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.98/1.16         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.98/1.16          | ~ (v13_waybel_0 @ X22 @ X23)
% 0.98/1.16          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.98/1.16          | (r2_hidden @ X24 @ X22)
% 0.98/1.16          | ~ (r1_orders_2 @ X23 @ X25 @ X24)
% 0.98/1.16          | ~ (r2_hidden @ X25 @ X22)
% 0.98/1.16          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.98/1.16          | ~ (l1_orders_2 @ X23))),
% 0.98/1.16      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.98/1.16  thf('59', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]:
% 0.98/1.16         (~ (l1_orders_2 @ sk_A)
% 0.98/1.16          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.16          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.16          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.98/1.16          | (r2_hidden @ X1 @ sk_B_1)
% 0.98/1.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.98/1.16          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.98/1.16      inference('sup-', [status(thm)], ['57', '58'])).
% 0.98/1.16  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('61', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('62', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]:
% 0.98/1.16         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.16          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.16          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.98/1.16          | (r2_hidden @ X1 @ sk_B_1)
% 0.98/1.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.98/1.16  thf('63', plain,
% 0.98/1.16      ((![X0 : $i]:
% 0.98/1.16          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.16           | (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.16           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.98/1.16           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['56', '62'])).
% 0.98/1.16  thf('64', plain,
% 0.98/1.16      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('split', [status(esa)], ['0'])).
% 0.98/1.16  thf('65', plain,
% 0.98/1.16      ((![X0 : $i]:
% 0.98/1.16          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.16           | (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.16           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('demod', [status(thm)], ['63', '64'])).
% 0.98/1.16  thf('66', plain,
% 0.98/1.16      ((![X0 : $i]:
% 0.98/1.16          (~ (l1_orders_2 @ sk_A)
% 0.98/1.16           | (v2_struct_0 @ sk_A)
% 0.98/1.16           | ~ (v5_orders_2 @ sk_A)
% 0.98/1.16           | ~ (v1_yellow_0 @ sk_A)
% 0.98/1.16           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.98/1.16           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['51', '65'])).
% 0.98/1.16  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('69', plain, ((v1_yellow_0 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('70', plain,
% 0.98/1.16      ((![X0 : $i]:
% 0.98/1.16          ((v2_struct_0 @ sk_A)
% 0.98/1.16           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.98/1.16           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.98/1.16  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('72', plain,
% 0.98/1.16      ((![X0 : $i]:
% 0.98/1.16          (~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.98/1.16           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('clc', [status(thm)], ['70', '71'])).
% 0.98/1.16  thf('73', plain,
% 0.98/1.16      ((![X0 : $i]:
% 0.98/1.16          (~ (l1_orders_2 @ sk_A)
% 0.98/1.16           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['31', '72'])).
% 0.98/1.16  thf('74', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('75', plain,
% 0.98/1.16      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('demod', [status(thm)], ['73', '74'])).
% 0.98/1.16  thf('76', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.16          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.98/1.16      inference('sup-', [status(thm)], ['53', '54'])).
% 0.98/1.16  thf('77', plain,
% 0.98/1.16      ((![X0 : $i]:
% 0.98/1.16          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['75', '76'])).
% 0.98/1.16  thf('78', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i]:
% 0.98/1.16         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.16          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.16          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.98/1.16          | (r2_hidden @ X1 @ sk_B_1)
% 0.98/1.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.98/1.16  thf('79', plain,
% 0.98/1.16      ((![X0 : $i, X1 : $i]:
% 0.98/1.16          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.98/1.16           | (r2_hidden @ X1 @ sk_B_1)
% 0.98/1.16           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.98/1.16           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['77', '78'])).
% 0.98/1.16  thf('80', plain,
% 0.98/1.16      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('demod', [status(thm)], ['73', '74'])).
% 0.98/1.16  thf('81', plain,
% 0.98/1.16      ((![X0 : $i, X1 : $i]:
% 0.98/1.16          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.98/1.16           | (r2_hidden @ X1 @ sk_B_1)
% 0.98/1.16           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('demod', [status(thm)], ['79', '80'])).
% 0.98/1.16  thf('82', plain,
% 0.98/1.16      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16         | (r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.98/1.16         | ~ (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.16              (u1_struct_0 @ sk_A))))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['30', '81'])).
% 0.98/1.16  thf('83', plain,
% 0.98/1.16      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.16           (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['3', '4'])).
% 0.98/1.16  thf('84', plain,
% 0.98/1.16      ((((r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.98/1.16         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('clc', [status(thm)], ['82', '83'])).
% 0.98/1.16  thf('85', plain,
% 0.98/1.16      (![X3 : $i, X4 : $i]:
% 0.98/1.16         (~ (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.98/1.16          | ((X4) = (X3))
% 0.98/1.16          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.98/1.16      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.98/1.16  thf('86', plain,
% 0.98/1.16      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.16         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['84', '85'])).
% 0.98/1.16  thf('87', plain,
% 0.98/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('88', plain,
% 0.98/1.16      (((((u1_struct_0 @ sk_A) = (sk_B_1)) | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('demod', [status(thm)], ['86', '87'])).
% 0.98/1.16  thf('89', plain,
% 0.98/1.16      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('simplify', [status(thm)], ['88'])).
% 0.98/1.16  thf('90', plain,
% 0.98/1.16      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.98/1.16        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('91', plain,
% 0.98/1.16      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.16         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.16      inference('split', [status(esa)], ['90'])).
% 0.98/1.16  thf('92', plain,
% 0.98/1.16      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.98/1.16         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.98/1.16             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('sup+', [status(thm)], ['89', '91'])).
% 0.98/1.16  thf('93', plain,
% 0.98/1.16      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 0.98/1.16         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.16      inference('simplify', [status(thm)], ['88'])).
% 0.98/1.17  thf('94', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('95', plain,
% 0.98/1.17      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.98/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.17      inference('sup+', [status(thm)], ['93', '94'])).
% 0.98/1.17  thf(d7_subset_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.17       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.98/1.17  thf('96', plain,
% 0.98/1.17      (![X26 : $i, X27 : $i]:
% 0.98/1.17         (~ (v1_subset_1 @ X27 @ X26)
% 0.98/1.17          | ((X27) != (X26))
% 0.98/1.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.98/1.17      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.98/1.17  thf('97', plain,
% 0.98/1.17      (![X26 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))
% 0.98/1.17          | ~ (v1_subset_1 @ X26 @ X26))),
% 0.98/1.17      inference('simplify', [status(thm)], ['96'])).
% 0.98/1.17  thf('98', plain,
% 0.98/1.17      ((~ (v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.98/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['95', '97'])).
% 0.98/1.17  thf('99', plain,
% 0.98/1.17      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.98/1.17       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['92', '98'])).
% 0.98/1.17  thf('100', plain,
% 0.98/1.17      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.98/1.17       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('split', [status(esa)], ['90'])).
% 0.98/1.17  thf('101', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('102', plain,
% 0.98/1.17      (![X26 : $i, X27 : $i]:
% 0.98/1.17         (((X27) = (X26))
% 0.98/1.17          | (v1_subset_1 @ X27 @ X26)
% 0.98/1.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.98/1.17      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.98/1.17  thf('103', plain,
% 0.98/1.17      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.98/1.17        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['101', '102'])).
% 0.98/1.17  thf('104', plain,
% 0.98/1.17      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.17         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.17      inference('split', [status(esa)], ['0'])).
% 0.98/1.17  thf('105', plain,
% 0.98/1.17      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.98/1.17         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.17      inference('sup-', [status(thm)], ['103', '104'])).
% 0.98/1.17  thf('106', plain,
% 0.98/1.17      (![X14 : $i]:
% 0.98/1.17         (((k3_yellow_0 @ X14) = (k1_yellow_0 @ X14 @ k1_xboole_0))
% 0.98/1.17          | ~ (l1_orders_2 @ X14))),
% 0.98/1.17      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.98/1.17  thf('107', plain,
% 0.98/1.17      (![X19 : $i, X20 : $i]:
% 0.98/1.17         (~ (l1_orders_2 @ X19)
% 0.98/1.17          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 0.98/1.17      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.98/1.17  thf('108', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 0.98/1.17          | ~ (l1_orders_2 @ X0)
% 0.98/1.17          | ~ (l1_orders_2 @ X0))),
% 0.98/1.17      inference('sup+', [status(thm)], ['106', '107'])).
% 0.98/1.17  thf('109', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (l1_orders_2 @ X0)
% 0.98/1.17          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.98/1.17      inference('simplify', [status(thm)], ['108'])).
% 0.98/1.17  thf(t2_subset, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ A @ B ) =>
% 0.98/1.17       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.98/1.17  thf('110', plain,
% 0.98/1.17      (![X5 : $i, X6 : $i]:
% 0.98/1.17         ((r2_hidden @ X5 @ X6)
% 0.98/1.17          | (v1_xboole_0 @ X6)
% 0.98/1.17          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.98/1.17      inference('cnf', [status(esa)], [t2_subset])).
% 0.98/1.17  thf('111', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (l1_orders_2 @ X0)
% 0.98/1.17          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.98/1.17          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['109', '110'])).
% 0.98/1.17  thf('112', plain,
% 0.98/1.17      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.98/1.17         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.98/1.17         | ~ (l1_orders_2 @ sk_A)))
% 0.98/1.17         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.17      inference('sup+', [status(thm)], ['105', '111'])).
% 0.98/1.17  thf('113', plain,
% 0.98/1.17      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.98/1.17         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.17      inference('sup-', [status(thm)], ['103', '104'])).
% 0.98/1.17  thf('114', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('115', plain,
% 0.98/1.17      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 0.98/1.17         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.17      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.98/1.17  thf('116', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('117', plain,
% 0.98/1.17      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.98/1.17         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.17      inference('clc', [status(thm)], ['115', '116'])).
% 0.98/1.17  thf('118', plain,
% 0.98/1.17      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.98/1.17         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.17      inference('split', [status(esa)], ['90'])).
% 0.98/1.17  thf('119', plain,
% 0.98/1.17      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.98/1.17       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['117', '118'])).
% 0.98/1.17  thf('120', plain, ($false),
% 0.98/1.17      inference('sat_resolution*', [status(thm)], ['1', '99', '100', '119'])).
% 0.98/1.17  
% 0.98/1.17  % SZS output end Refutation
% 0.98/1.17  
% 0.98/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
