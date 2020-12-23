%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.02LVSVEUhN

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:09 EST 2020

% Result     : Theorem 11.10s
% Output     : Refutation 11.10s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 602 expanded)
%              Number of leaves         :   44 ( 188 expanded)
%              Depth                    :   28
%              Number of atoms          : 2131 (8665 expanded)
%              Number of equality atoms :   36 (  89 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

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
    ! [X31: $i] :
      ( ( r1_yellow_0 @ X31 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v1_yellow_0 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t8_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( X11 = X9 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X11 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

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

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X20 @ X22 @ X21 ) @ X22 )
      | ( r2_lattice3 @ X21 @ X22 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
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

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X27
       != ( k1_yellow_0 @ X25 @ X26 ) )
      | ~ ( r2_lattice3 @ X25 @ X26 @ X28 )
      | ( r1_orders_2 @ X25 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_yellow_0 @ X25 @ X26 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('20',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X25 )
      | ~ ( r1_yellow_0 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X25 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ( r1_orders_2 @ X25 @ ( k1_yellow_0 @ X25 @ X26 ) @ X28 )
      | ~ ( r2_lattice3 @ X25 @ X26 @ X28 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','27'])).

thf('29',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X24: $i] :
      ( ( ( k3_yellow_0 @ X24 )
        = ( k1_yellow_0 @ X24 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('38',plain,(
    ! [X31: $i] :
      ( ( r1_yellow_0 @ X31 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v1_yellow_0 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X20 @ X22 @ X21 ) @ X22 )
      | ( r2_lattice3 @ X21 @ X22 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k1_yellow_0 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ X2 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r2_hidden @ ( sk_C @ X32 @ X33 ) @ X32 )
      | ( v13_waybel_0 @ X32 @ X33 )
      | ~ ( l1_orders_2 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('63',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) )
      | ( v13_waybel_0 @ X32 @ X33 )
      | ~ ( l1_orders_2 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D_3 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_3 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('68',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r2_hidden @ ( sk_D_3 @ X32 @ X33 ) @ X32 )
      | ( v13_waybel_0 @ X32 @ X33 )
      | ~ ( l1_orders_2 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_3 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['61','71'])).

thf('73',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('75',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('79',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('83',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v13_waybel_0 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ( r2_hidden @ X34 @ X32 )
      | ~ ( r1_orders_2 @ X33 @ X35 @ X34 )
      | ~ ( r2_hidden @ X35 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','88'])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','91'])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','98'])).

thf('100',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v13_waybel_0 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ( r2_hidden @ X34 @ X32 )
      | ~ ( r1_orders_2 @ X33 @ X35 @ X34 )
      | ~ ( r2_hidden @ X35 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('112',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','124'])).

thf('126',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('129',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( X11 = X9 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X11 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X11 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('133',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['126','133'])).

thf('135',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('136',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['137'])).

thf('139',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['136','138'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('140',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_subset_1 @ X37 @ X36 )
      | ( X37 != X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('141',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( v1_subset_1 @ X36 @ X36 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('143',plain,(
    ! [X36: $i] :
      ~ ( v1_subset_1 @ X36 @ X36 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','143'])).

thf('145',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['137'])).

thf('146',plain,(
    ! [X24: $i] :
      ( ( ( k3_yellow_0 @ X24 )
        = ( k1_yellow_0 @ X24 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('147',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37 = X36 )
      | ( v1_subset_1 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('149',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('151',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['146','155'])).

thf('157',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('160',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['137'])).

thf('164',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','144','145','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.02LVSVEUhN
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 11.10/11.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.10/11.29  % Solved by: fo/fo7.sh
% 11.10/11.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.10/11.29  % done 4258 iterations in 10.821s
% 11.10/11.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.10/11.29  % SZS output start Refutation
% 11.10/11.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.10/11.29  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 11.10/11.29  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 11.10/11.29  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 11.10/11.29  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 11.10/11.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.10/11.29  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 11.10/11.29  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 11.10/11.29  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 11.10/11.29  thf(sk_A_type, type, sk_A: $i).
% 11.10/11.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.10/11.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.10/11.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 11.10/11.29  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 11.10/11.29  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 11.10/11.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.10/11.29  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 11.10/11.29  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 11.10/11.29  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 11.10/11.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.10/11.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.10/11.29  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 11.10/11.29  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 11.10/11.29  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.10/11.29  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 11.10/11.29  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 11.10/11.29  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 11.10/11.29  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 11.10/11.29  thf(t8_waybel_7, conjecture,
% 11.10/11.29    (![A:$i]:
% 11.10/11.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 11.10/11.29         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 11.10/11.29         ( l1_orders_2 @ A ) ) =>
% 11.10/11.29       ( ![B:$i]:
% 11.10/11.29         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 11.10/11.29             ( v13_waybel_0 @ B @ A ) & 
% 11.10/11.29             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.10/11.29           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 11.10/11.29             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 11.10/11.29  thf(zf_stmt_0, negated_conjecture,
% 11.10/11.29    (~( ![A:$i]:
% 11.10/11.29        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 11.10/11.29            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 11.10/11.29            ( l1_orders_2 @ A ) ) =>
% 11.10/11.29          ( ![B:$i]:
% 11.10/11.29            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 11.10/11.29                ( v13_waybel_0 @ B @ A ) & 
% 11.10/11.29                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.10/11.29              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 11.10/11.29                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 11.10/11.29    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 11.10/11.29  thf('0', plain,
% 11.10/11.29      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 11.10/11.29        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('1', plain,
% 11.10/11.29      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 11.10/11.29       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('split', [status(esa)], ['0'])).
% 11.10/11.29  thf(t42_yellow_0, axiom,
% 11.10/11.29    (![A:$i]:
% 11.10/11.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 11.10/11.29         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.10/11.29       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 11.10/11.29         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 11.10/11.29  thf('2', plain,
% 11.10/11.29      (![X31 : $i]:
% 11.10/11.29         ((r1_yellow_0 @ X31 @ k1_xboole_0)
% 11.10/11.29          | ~ (l1_orders_2 @ X31)
% 11.10/11.29          | ~ (v1_yellow_0 @ X31)
% 11.10/11.29          | ~ (v5_orders_2 @ X31)
% 11.10/11.29          | (v2_struct_0 @ X31))),
% 11.10/11.29      inference('cnf', [status(esa)], [t42_yellow_0])).
% 11.10/11.29  thf('3', plain,
% 11.10/11.29      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf(d10_xboole_0, axiom,
% 11.10/11.29    (![A:$i,B:$i]:
% 11.10/11.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.10/11.29  thf('4', plain,
% 11.10/11.29      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 11.10/11.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.10/11.29  thf('5', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 11.10/11.29      inference('simplify', [status(thm)], ['4'])).
% 11.10/11.29  thf(t3_subset, axiom,
% 11.10/11.29    (![A:$i,B:$i]:
% 11.10/11.29     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 11.10/11.29  thf('6', plain,
% 11.10/11.29      (![X14 : $i, X16 : $i]:
% 11.10/11.29         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 11.10/11.29      inference('cnf', [status(esa)], [t3_subset])).
% 11.10/11.29  thf('7', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['5', '6'])).
% 11.10/11.29  thf(t8_subset_1, axiom,
% 11.10/11.29    (![A:$i,B:$i]:
% 11.10/11.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.10/11.29       ( ![C:$i]:
% 11.10/11.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 11.10/11.29           ( ( ![D:$i]:
% 11.10/11.29               ( ( m1_subset_1 @ D @ A ) =>
% 11.10/11.29                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 11.10/11.29             ( ( B ) = ( C ) ) ) ) ) ))).
% 11.10/11.29  thf('8', plain,
% 11.10/11.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 11.10/11.29          | ((X11) = (X9))
% 11.10/11.29          | (m1_subset_1 @ (sk_D @ X9 @ X11 @ X10) @ X10)
% 11.10/11.29          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 11.10/11.29      inference('cnf', [status(esa)], [t8_subset_1])).
% 11.10/11.29  thf('9', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 11.10/11.29          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 11.10/11.29          | ((X1) = (X0)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['7', '8'])).
% 11.10/11.29  thf('10', plain,
% 11.10/11.29      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29        | (m1_subset_1 @ 
% 11.10/11.29           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29           (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['3', '9'])).
% 11.10/11.29  thf(d9_lattice3, axiom,
% 11.10/11.29    (![A:$i]:
% 11.10/11.29     ( ( l1_orders_2 @ A ) =>
% 11.10/11.29       ( ![B:$i,C:$i]:
% 11.10/11.29         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.10/11.29           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 11.10/11.29             ( ![D:$i]:
% 11.10/11.29               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.10/11.29                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 11.10/11.29  thf('11', plain,
% 11.10/11.29      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 11.10/11.29          | (r2_hidden @ (sk_D_1 @ X20 @ X22 @ X21) @ X22)
% 11.10/11.29          | (r2_lattice3 @ X21 @ X22 @ X20)
% 11.10/11.29          | ~ (l1_orders_2 @ X21))),
% 11.10/11.29      inference('cnf', [status(esa)], [d9_lattice3])).
% 11.10/11.29  thf('12', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (l1_orders_2 @ sk_A)
% 11.10/11.29          | (r2_lattice3 @ sk_A @ X0 @ 
% 11.10/11.29             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | (r2_hidden @ 
% 11.10/11.29             (sk_D_1 @ 
% 11.10/11.29              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29              X0 @ sk_A) @ 
% 11.10/11.29             X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['10', '11'])).
% 11.10/11.29  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('14', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29          | (r2_lattice3 @ sk_A @ X0 @ 
% 11.10/11.29             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | (r2_hidden @ 
% 11.10/11.29             (sk_D_1 @ 
% 11.10/11.29              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29              X0 @ sk_A) @ 
% 11.10/11.29             X0))),
% 11.10/11.29      inference('demod', [status(thm)], ['12', '13'])).
% 11.10/11.29  thf(d1_xboole_0, axiom,
% 11.10/11.29    (![A:$i]:
% 11.10/11.29     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 11.10/11.29  thf('15', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.10/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.10/11.29  thf('16', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         ((r2_lattice3 @ sk_A @ X0 @ 
% 11.10/11.29           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (v1_xboole_0 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['14', '15'])).
% 11.10/11.29  thf('17', plain,
% 11.10/11.29      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29        | (m1_subset_1 @ 
% 11.10/11.29           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29           (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['3', '9'])).
% 11.10/11.29  thf(dt_k1_yellow_0, axiom,
% 11.10/11.29    (![A:$i,B:$i]:
% 11.10/11.29     ( ( l1_orders_2 @ A ) =>
% 11.10/11.29       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 11.10/11.29  thf('18', plain,
% 11.10/11.29      (![X29 : $i, X30 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X29)
% 11.10/11.29          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 11.10/11.29      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 11.10/11.29  thf(d9_yellow_0, axiom,
% 11.10/11.29    (![A:$i]:
% 11.10/11.29     ( ( l1_orders_2 @ A ) =>
% 11.10/11.29       ( ![B:$i,C:$i]:
% 11.10/11.29         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.10/11.29           ( ( r1_yellow_0 @ A @ B ) =>
% 11.10/11.29             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 11.10/11.29               ( ( r2_lattice3 @ A @ B @ C ) & 
% 11.10/11.29                 ( ![D:$i]:
% 11.10/11.29                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.10/11.29                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 11.10/11.29                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 11.10/11.29  thf('19', plain,
% 11.10/11.29      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 11.10/11.29         (((X27) != (k1_yellow_0 @ X25 @ X26))
% 11.10/11.29          | ~ (r2_lattice3 @ X25 @ X26 @ X28)
% 11.10/11.29          | (r1_orders_2 @ X25 @ X27 @ X28)
% 11.10/11.29          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 11.10/11.29          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 11.10/11.29          | ~ (r1_yellow_0 @ X25 @ X26)
% 11.10/11.29          | ~ (l1_orders_2 @ X25))),
% 11.10/11.29      inference('cnf', [status(esa)], [d9_yellow_0])).
% 11.10/11.29  thf('20', plain,
% 11.10/11.29      (![X25 : $i, X26 : $i, X28 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X25)
% 11.10/11.29          | ~ (r1_yellow_0 @ X25 @ X26)
% 11.10/11.29          | ~ (m1_subset_1 @ (k1_yellow_0 @ X25 @ X26) @ (u1_struct_0 @ X25))
% 11.10/11.29          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 11.10/11.29          | (r1_orders_2 @ X25 @ (k1_yellow_0 @ X25 @ X26) @ X28)
% 11.10/11.29          | ~ (r2_lattice3 @ X25 @ X26 @ X28))),
% 11.10/11.29      inference('simplify', [status(thm)], ['19'])).
% 11.10/11.29  thf('21', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 11.10/11.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 11.10/11.29          | ~ (r1_yellow_0 @ X0 @ X1)
% 11.10/11.29          | ~ (l1_orders_2 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['18', '20'])).
% 11.10/11.29  thf('22', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (r1_yellow_0 @ X0 @ X1)
% 11.10/11.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 11.10/11.29          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 11.10/11.29          | ~ (l1_orders_2 @ X0))),
% 11.10/11.29      inference('simplify', [status(thm)], ['21'])).
% 11.10/11.29  thf('23', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (l1_orders_2 @ sk_A)
% 11.10/11.29          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 11.10/11.29               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 11.10/11.29             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['17', '22'])).
% 11.10/11.29  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('25', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 11.10/11.29               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 11.10/11.29             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 11.10/11.29      inference('demod', [status(thm)], ['23', '24'])).
% 11.10/11.29  thf('26', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (~ (v1_xboole_0 @ X0)
% 11.10/11.29          | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (r1_yellow_0 @ sk_A @ X0)
% 11.10/11.29          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 11.10/11.29             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['16', '25'])).
% 11.10/11.29  thf('27', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 11.10/11.29           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29          | ~ (r1_yellow_0 @ sk_A @ X0)
% 11.10/11.29          | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (v1_xboole_0 @ X0))),
% 11.10/11.29      inference('simplify', [status(thm)], ['26'])).
% 11.10/11.29  thf('28', plain,
% 11.10/11.29      (((v2_struct_0 @ sk_A)
% 11.10/11.29        | ~ (v5_orders_2 @ sk_A)
% 11.10/11.29        | ~ (v1_yellow_0 @ sk_A)
% 11.10/11.29        | ~ (l1_orders_2 @ sk_A)
% 11.10/11.29        | ~ (v1_xboole_0 @ k1_xboole_0)
% 11.10/11.29        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 11.10/11.29           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('sup-', [status(thm)], ['2', '27'])).
% 11.10/11.29  thf('29', plain, ((v5_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('30', plain, ((v1_yellow_0 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 11.10/11.29  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.10/11.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.10/11.29  thf('33', plain,
% 11.10/11.29      (((v2_struct_0 @ sk_A)
% 11.10/11.29        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 11.10/11.29           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 11.10/11.29  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('35', plain,
% 11.10/11.29      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 11.10/11.29         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('clc', [status(thm)], ['33', '34'])).
% 11.10/11.29  thf('36', plain,
% 11.10/11.29      (![X29 : $i, X30 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X29)
% 11.10/11.29          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 11.10/11.29      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 11.10/11.29  thf(d11_yellow_0, axiom,
% 11.10/11.29    (![A:$i]:
% 11.10/11.29     ( ( l1_orders_2 @ A ) =>
% 11.10/11.29       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 11.10/11.29  thf('37', plain,
% 11.10/11.29      (![X24 : $i]:
% 11.10/11.29         (((k3_yellow_0 @ X24) = (k1_yellow_0 @ X24 @ k1_xboole_0))
% 11.10/11.29          | ~ (l1_orders_2 @ X24))),
% 11.10/11.29      inference('cnf', [status(esa)], [d11_yellow_0])).
% 11.10/11.29  thf('38', plain,
% 11.10/11.29      (![X31 : $i]:
% 11.10/11.29         ((r1_yellow_0 @ X31 @ k1_xboole_0)
% 11.10/11.29          | ~ (l1_orders_2 @ X31)
% 11.10/11.29          | ~ (v1_yellow_0 @ X31)
% 11.10/11.29          | ~ (v5_orders_2 @ X31)
% 11.10/11.29          | (v2_struct_0 @ X31))),
% 11.10/11.29      inference('cnf', [status(esa)], [t42_yellow_0])).
% 11.10/11.29  thf('39', plain,
% 11.10/11.29      (![X29 : $i, X30 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X29)
% 11.10/11.29          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 11.10/11.29      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 11.10/11.29  thf('40', plain,
% 11.10/11.29      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 11.10/11.29          | (r2_hidden @ (sk_D_1 @ X20 @ X22 @ X21) @ X22)
% 11.10/11.29          | (r2_lattice3 @ X21 @ X22 @ X20)
% 11.10/11.29          | ~ (l1_orders_2 @ X21))),
% 11.10/11.29      inference('cnf', [status(esa)], [d9_lattice3])).
% 11.10/11.29  thf('41', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 11.10/11.29          | (r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2))),
% 11.10/11.29      inference('sup-', [status(thm)], ['39', '40'])).
% 11.10/11.29  thf('42', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         ((r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2)
% 11.10/11.29          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 11.10/11.29          | ~ (l1_orders_2 @ X0))),
% 11.10/11.29      inference('simplify', [status(thm)], ['41'])).
% 11.10/11.29  thf('43', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.10/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.10/11.29  thf('44', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X1)
% 11.10/11.29          | (r2_lattice3 @ X1 @ X0 @ (k1_yellow_0 @ X1 @ X2))
% 11.10/11.29          | ~ (v1_xboole_0 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['42', '43'])).
% 11.10/11.29  thf('45', plain,
% 11.10/11.29      (![X29 : $i, X30 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X29)
% 11.10/11.29          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 11.10/11.29      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 11.10/11.29  thf('46', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (r1_yellow_0 @ X0 @ X1)
% 11.10/11.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 11.10/11.29          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 11.10/11.29          | ~ (l1_orders_2 @ X0))),
% 11.10/11.29      inference('simplify', [status(thm)], ['21'])).
% 11.10/11.29  thf('47', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 11.10/11.29             (k1_yellow_0 @ X0 @ X1))
% 11.10/11.29          | ~ (r1_yellow_0 @ X0 @ X2))),
% 11.10/11.29      inference('sup-', [status(thm)], ['45', '46'])).
% 11.10/11.29  thf('48', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (r1_yellow_0 @ X0 @ X2)
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 11.10/11.29             (k1_yellow_0 @ X0 @ X1))
% 11.10/11.29          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 11.10/11.29          | ~ (l1_orders_2 @ X0))),
% 11.10/11.29      inference('simplify', [status(thm)], ['47'])).
% 11.10/11.29  thf('49', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (v1_xboole_0 @ X2)
% 11.10/11.29          | ~ (l1_orders_2 @ X1)
% 11.10/11.29          | ~ (l1_orders_2 @ X1)
% 11.10/11.29          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 11.10/11.29             (k1_yellow_0 @ X1 @ X0))
% 11.10/11.29          | ~ (r1_yellow_0 @ X1 @ X2))),
% 11.10/11.29      inference('sup-', [status(thm)], ['44', '48'])).
% 11.10/11.29  thf('50', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (r1_yellow_0 @ X1 @ X2)
% 11.10/11.29          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 11.10/11.29             (k1_yellow_0 @ X1 @ X0))
% 11.10/11.29          | ~ (l1_orders_2 @ X1)
% 11.10/11.29          | ~ (v1_xboole_0 @ X2))),
% 11.10/11.29      inference('simplify', [status(thm)], ['49'])).
% 11.10/11.29  thf('51', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         ((v2_struct_0 @ X0)
% 11.10/11.29          | ~ (v5_orders_2 @ X0)
% 11.10/11.29          | ~ (v1_yellow_0 @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (v1_xboole_0 @ k1_xboole_0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 11.10/11.29             (k1_yellow_0 @ X0 @ X1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['38', '50'])).
% 11.10/11.29  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.10/11.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.10/11.29  thf('53', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         ((v2_struct_0 @ X0)
% 11.10/11.29          | ~ (v5_orders_2 @ X0)
% 11.10/11.29          | ~ (v1_yellow_0 @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 11.10/11.29             (k1_yellow_0 @ X0 @ X1)))),
% 11.10/11.29      inference('demod', [status(thm)], ['51', '52'])).
% 11.10/11.29  thf('54', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 11.10/11.29           (k1_yellow_0 @ X0 @ X1))
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (v1_yellow_0 @ X0)
% 11.10/11.29          | ~ (v5_orders_2 @ X0)
% 11.10/11.29          | (v2_struct_0 @ X0))),
% 11.10/11.29      inference('simplify', [status(thm)], ['53'])).
% 11.10/11.29  thf('55', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (v2_struct_0 @ X0)
% 11.10/11.29          | ~ (v5_orders_2 @ X0)
% 11.10/11.29          | ~ (v1_yellow_0 @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0))),
% 11.10/11.29      inference('sup+', [status(thm)], ['37', '54'])).
% 11.10/11.29  thf('56', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         (~ (v1_yellow_0 @ X0)
% 11.10/11.29          | ~ (v5_orders_2 @ X0)
% 11.10/11.29          | (v2_struct_0 @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 11.10/11.29      inference('simplify', [status(thm)], ['55'])).
% 11.10/11.29  thf('57', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['5', '6'])).
% 11.10/11.29  thf(d20_waybel_0, axiom,
% 11.10/11.29    (![A:$i]:
% 11.10/11.29     ( ( l1_orders_2 @ A ) =>
% 11.10/11.29       ( ![B:$i]:
% 11.10/11.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.10/11.29           ( ( v13_waybel_0 @ B @ A ) <=>
% 11.10/11.29             ( ![C:$i]:
% 11.10/11.29               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.10/11.29                 ( ![D:$i]:
% 11.10/11.29                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.10/11.29                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 11.10/11.29                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 11.10/11.29  thf('58', plain,
% 11.10/11.29      (![X32 : $i, X33 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 11.10/11.29          | (r2_hidden @ (sk_C @ X32 @ X33) @ X32)
% 11.10/11.29          | (v13_waybel_0 @ X32 @ X33)
% 11.10/11.29          | ~ (l1_orders_2 @ X33))),
% 11.10/11.29      inference('cnf', [status(esa)], [d20_waybel_0])).
% 11.10/11.29  thf('59', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X0)
% 11.10/11.29          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 11.10/11.29          | (r2_hidden @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['57', '58'])).
% 11.10/11.29  thf('60', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.10/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.10/11.29  thf('61', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['59', '60'])).
% 11.10/11.29  thf('62', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['5', '6'])).
% 11.10/11.29  thf('63', plain,
% 11.10/11.29      (![X32 : $i, X33 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 11.10/11.29          | (m1_subset_1 @ (sk_D_3 @ X32 @ X33) @ (u1_struct_0 @ X33))
% 11.10/11.29          | (v13_waybel_0 @ X32 @ X33)
% 11.10/11.29          | ~ (l1_orders_2 @ X33))),
% 11.10/11.29      inference('cnf', [status(esa)], [d20_waybel_0])).
% 11.10/11.29  thf('64', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X0)
% 11.10/11.29          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 11.10/11.29          | (m1_subset_1 @ (sk_D_3 @ (u1_struct_0 @ X0) @ X0) @ 
% 11.10/11.29             (u1_struct_0 @ X0)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['62', '63'])).
% 11.10/11.29  thf(t2_subset, axiom,
% 11.10/11.29    (![A:$i,B:$i]:
% 11.10/11.29     ( ( m1_subset_1 @ A @ B ) =>
% 11.10/11.29       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 11.10/11.29  thf('65', plain,
% 11.10/11.29      (![X12 : $i, X13 : $i]:
% 11.10/11.29         ((r2_hidden @ X12 @ X13)
% 11.10/11.29          | (v1_xboole_0 @ X13)
% 11.10/11.29          | ~ (m1_subset_1 @ X12 @ X13))),
% 11.10/11.29      inference('cnf', [status(esa)], [t2_subset])).
% 11.10/11.29  thf('66', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 11.10/11.29          | (r2_hidden @ (sk_D_3 @ (u1_struct_0 @ X0) @ X0) @ 
% 11.10/11.29             (u1_struct_0 @ X0)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['64', '65'])).
% 11.10/11.29  thf('67', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['5', '6'])).
% 11.10/11.29  thf('68', plain,
% 11.10/11.29      (![X32 : $i, X33 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 11.10/11.29          | ~ (r2_hidden @ (sk_D_3 @ X32 @ X33) @ X32)
% 11.10/11.29          | (v13_waybel_0 @ X32 @ X33)
% 11.10/11.29          | ~ (l1_orders_2 @ X33))),
% 11.10/11.29      inference('cnf', [status(esa)], [d20_waybel_0])).
% 11.10/11.29  thf('69', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X0)
% 11.10/11.29          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 11.10/11.29          | ~ (r2_hidden @ (sk_D_3 @ (u1_struct_0 @ X0) @ X0) @ 
% 11.10/11.29               (u1_struct_0 @ X0)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['67', '68'])).
% 11.10/11.29  thf('70', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 11.10/11.29          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['66', '69'])).
% 11.10/11.29  thf('71', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 11.10/11.29      inference('simplify', [status(thm)], ['70'])).
% 11.10/11.29  thf('72', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X0) | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 11.10/11.29      inference('clc', [status(thm)], ['61', '71'])).
% 11.10/11.29  thf('73', plain,
% 11.10/11.29      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('split', [status(esa)], ['0'])).
% 11.10/11.29  thf('74', plain,
% 11.10/11.29      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf(l3_subset_1, axiom,
% 11.10/11.29    (![A:$i,B:$i]:
% 11.10/11.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.10/11.29       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 11.10/11.29  thf('75', plain,
% 11.10/11.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.10/11.29         (~ (r2_hidden @ X6 @ X7)
% 11.10/11.29          | (r2_hidden @ X6 @ X8)
% 11.10/11.29          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 11.10/11.29      inference('cnf', [status(esa)], [l3_subset_1])).
% 11.10/11.29  thf('76', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 11.10/11.29      inference('sup-', [status(thm)], ['74', '75'])).
% 11.10/11.29  thf('77', plain,
% 11.10/11.29      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['73', '76'])).
% 11.10/11.29  thf('78', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['5', '6'])).
% 11.10/11.29  thf(t4_subset, axiom,
% 11.10/11.29    (![A:$i,B:$i,C:$i]:
% 11.10/11.29     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 11.10/11.29       ( m1_subset_1 @ A @ C ) ))).
% 11.10/11.29  thf('79', plain,
% 11.10/11.29      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.10/11.29         (~ (r2_hidden @ X17 @ X18)
% 11.10/11.29          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 11.10/11.29          | (m1_subset_1 @ X17 @ X19))),
% 11.10/11.29      inference('cnf', [status(esa)], [t4_subset])).
% 11.10/11.29  thf('80', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['78', '79'])).
% 11.10/11.29  thf('81', plain,
% 11.10/11.29      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['77', '80'])).
% 11.10/11.29  thf('82', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['5', '6'])).
% 11.10/11.29  thf('83', plain,
% 11.10/11.29      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 11.10/11.29          | ~ (v13_waybel_0 @ X32 @ X33)
% 11.10/11.29          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 11.10/11.29          | (r2_hidden @ X34 @ X32)
% 11.10/11.29          | ~ (r1_orders_2 @ X33 @ X35 @ X34)
% 11.10/11.29          | ~ (r2_hidden @ X35 @ X32)
% 11.10/11.29          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 11.10/11.29          | ~ (l1_orders_2 @ X33))),
% 11.10/11.29      inference('cnf', [status(esa)], [d20_waybel_0])).
% 11.10/11.29  thf('84', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X0)
% 11.10/11.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 11.10/11.29          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 11.10/11.29          | ~ (r1_orders_2 @ X0 @ X1 @ X2)
% 11.10/11.29          | (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 11.10/11.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 11.10/11.29          | ~ (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['82', '83'])).
% 11.10/11.29  thf('85', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 11.10/11.29           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 11.10/11.29           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | ~ (l1_orders_2 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['81', '84'])).
% 11.10/11.29  thf('86', plain,
% 11.10/11.29      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['73', '76'])).
% 11.10/11.29  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('88', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 11.10/11.29           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('demod', [status(thm)], ['85', '86', '87'])).
% 11.10/11.29  thf('89', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (l1_orders_2 @ sk_A)
% 11.10/11.29           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 11.10/11.29           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['72', '88'])).
% 11.10/11.29  thf('90', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('91', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 11.10/11.29           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('demod', [status(thm)], ['89', '90'])).
% 11.10/11.29  thf('92', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (l1_orders_2 @ sk_A)
% 11.10/11.29           | (v2_struct_0 @ sk_A)
% 11.10/11.29           | ~ (v5_orders_2 @ sk_A)
% 11.10/11.29           | ~ (v1_yellow_0 @ sk_A)
% 11.10/11.29           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['56', '91'])).
% 11.10/11.29  thf('93', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('95', plain, ((v1_yellow_0 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('96', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          ((v2_struct_0 @ sk_A)
% 11.10/11.29           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 11.10/11.29  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('98', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('clc', [status(thm)], ['96', '97'])).
% 11.10/11.29  thf('99', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (l1_orders_2 @ sk_A)
% 11.10/11.29           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['36', '98'])).
% 11.10/11.29  thf('100', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('101', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('demod', [status(thm)], ['99', '100'])).
% 11.10/11.29  thf('102', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['78', '79'])).
% 11.10/11.29  thf('103', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['101', '102'])).
% 11.10/11.29  thf('104', plain,
% 11.10/11.29      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('105', plain,
% 11.10/11.29      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 11.10/11.29          | ~ (v13_waybel_0 @ X32 @ X33)
% 11.10/11.29          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 11.10/11.29          | (r2_hidden @ X34 @ X32)
% 11.10/11.29          | ~ (r1_orders_2 @ X33 @ X35 @ X34)
% 11.10/11.29          | ~ (r2_hidden @ X35 @ X32)
% 11.10/11.29          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 11.10/11.29          | ~ (l1_orders_2 @ X33))),
% 11.10/11.29      inference('cnf', [status(esa)], [d20_waybel_0])).
% 11.10/11.29  thf('106', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ sk_A)
% 11.10/11.29          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (r2_hidden @ X0 @ sk_B_1)
% 11.10/11.29          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 11.10/11.29          | (r2_hidden @ X1 @ sk_B_1)
% 11.10/11.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 11.10/11.29      inference('sup-', [status(thm)], ['104', '105'])).
% 11.10/11.29  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('108', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('109', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (r2_hidden @ X0 @ sk_B_1)
% 11.10/11.29          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 11.10/11.29          | (r2_hidden @ X1 @ sk_B_1)
% 11.10/11.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('demod', [status(thm)], ['106', '107', '108'])).
% 11.10/11.29  thf('110', plain,
% 11.10/11.29      ((![X0 : $i, X1 : $i]:
% 11.10/11.29          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | (r2_hidden @ X1 @ sk_B_1)
% 11.10/11.29           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 11.10/11.29           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['103', '109'])).
% 11.10/11.29  thf('111', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         (~ (v1_yellow_0 @ X0)
% 11.10/11.29          | ~ (v5_orders_2 @ X0)
% 11.10/11.29          | (v2_struct_0 @ X0)
% 11.10/11.29          | ~ (l1_orders_2 @ X0)
% 11.10/11.29          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 11.10/11.29      inference('simplify', [status(thm)], ['55'])).
% 11.10/11.29  thf('112', plain,
% 11.10/11.29      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['77', '80'])).
% 11.10/11.29  thf('113', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29          | ~ (r2_hidden @ X0 @ sk_B_1)
% 11.10/11.29          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 11.10/11.29          | (r2_hidden @ X1 @ sk_B_1)
% 11.10/11.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('demod', [status(thm)], ['106', '107', '108'])).
% 11.10/11.29  thf('114', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | (r2_hidden @ X0 @ sk_B_1)
% 11.10/11.29           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 11.10/11.29           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['112', '113'])).
% 11.10/11.29  thf('115', plain,
% 11.10/11.29      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('split', [status(esa)], ['0'])).
% 11.10/11.29  thf('116', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | (r2_hidden @ X0 @ sk_B_1)
% 11.10/11.29           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('demod', [status(thm)], ['114', '115'])).
% 11.10/11.29  thf('117', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (~ (l1_orders_2 @ sk_A)
% 11.10/11.29           | (v2_struct_0 @ sk_A)
% 11.10/11.29           | ~ (v5_orders_2 @ sk_A)
% 11.10/11.29           | ~ (v1_yellow_0 @ sk_A)
% 11.10/11.29           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 11.10/11.29           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['111', '116'])).
% 11.10/11.29  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('119', plain, ((v5_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('120', plain, ((v1_yellow_0 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('121', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['101', '102'])).
% 11.10/11.29  thf('122', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          ((v2_struct_0 @ sk_A)
% 11.10/11.29           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 11.10/11.29  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('124', plain,
% 11.10/11.29      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('clc', [status(thm)], ['122', '123'])).
% 11.10/11.29  thf('125', plain,
% 11.10/11.29      ((![X0 : $i, X1 : $i]:
% 11.10/11.29          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 11.10/11.29           | (r2_hidden @ X1 @ sk_B_1)
% 11.10/11.29           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('demod', [status(thm)], ['110', '124'])).
% 11.10/11.29  thf('126', plain,
% 11.10/11.29      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29         | (r2_hidden @ 
% 11.10/11.29            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29            sk_B_1)
% 11.10/11.29         | ~ (m1_subset_1 @ 
% 11.10/11.29              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29              (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['35', '125'])).
% 11.10/11.29  thf('127', plain,
% 11.10/11.29      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('128', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['5', '6'])).
% 11.10/11.29  thf('129', plain,
% 11.10/11.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 11.10/11.29          | ((X11) = (X9))
% 11.10/11.29          | ~ (r2_hidden @ (sk_D @ X9 @ X11 @ X10) @ X11)
% 11.10/11.29          | ~ (r2_hidden @ (sk_D @ X9 @ X11 @ X10) @ X9)
% 11.10/11.29          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 11.10/11.29      inference('cnf', [status(esa)], [t8_subset_1])).
% 11.10/11.29  thf('130', plain,
% 11.10/11.29      (![X0 : $i, X1 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 11.10/11.29          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 11.10/11.29          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 11.10/11.29          | ((X1) = (X0)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['128', '129'])).
% 11.10/11.29  thf('131', plain,
% 11.10/11.29      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29        | ~ (r2_hidden @ 
% 11.10/11.29             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29             sk_B_1)
% 11.10/11.29        | ~ (r2_hidden @ 
% 11.10/11.29             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29             (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['127', '130'])).
% 11.10/11.29  thf('132', plain,
% 11.10/11.29      (![X0 : $i]:
% 11.10/11.29         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 11.10/11.29      inference('sup-', [status(thm)], ['74', '75'])).
% 11.10/11.29  thf('133', plain,
% 11.10/11.29      ((~ (r2_hidden @ 
% 11.10/11.29           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29           sk_B_1)
% 11.10/11.29        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('clc', [status(thm)], ['131', '132'])).
% 11.10/11.29  thf('134', plain,
% 11.10/11.29      (((~ (m1_subset_1 @ 
% 11.10/11.29            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29            (u1_struct_0 @ sk_A))
% 11.10/11.29         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('clc', [status(thm)], ['126', '133'])).
% 11.10/11.29  thf('135', plain,
% 11.10/11.29      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 11.10/11.29        | (m1_subset_1 @ 
% 11.10/11.29           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 11.10/11.29           (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['3', '9'])).
% 11.10/11.29  thf('136', plain,
% 11.10/11.29      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('clc', [status(thm)], ['134', '135'])).
% 11.10/11.29  thf('137', plain,
% 11.10/11.29      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 11.10/11.29        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('138', plain,
% 11.10/11.29      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('split', [status(esa)], ['137'])).
% 11.10/11.29  thf('139', plain,
% 11.10/11.29      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 11.10/11.29         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 11.10/11.29             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('sup+', [status(thm)], ['136', '138'])).
% 11.10/11.29  thf(d7_subset_1, axiom,
% 11.10/11.29    (![A:$i,B:$i]:
% 11.10/11.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.10/11.29       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 11.10/11.29  thf('140', plain,
% 11.10/11.29      (![X36 : $i, X37 : $i]:
% 11.10/11.29         (~ (v1_subset_1 @ X37 @ X36)
% 11.10/11.29          | ((X37) != (X36))
% 11.10/11.29          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 11.10/11.29      inference('cnf', [status(esa)], [d7_subset_1])).
% 11.10/11.29  thf('141', plain,
% 11.10/11.29      (![X36 : $i]:
% 11.10/11.29         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))
% 11.10/11.29          | ~ (v1_subset_1 @ X36 @ X36))),
% 11.10/11.29      inference('simplify', [status(thm)], ['140'])).
% 11.10/11.29  thf('142', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.10/11.29      inference('sup-', [status(thm)], ['5', '6'])).
% 11.10/11.29  thf('143', plain, (![X36 : $i]: ~ (v1_subset_1 @ X36 @ X36)),
% 11.10/11.29      inference('demod', [status(thm)], ['141', '142'])).
% 11.10/11.29  thf('144', plain,
% 11.10/11.29      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 11.10/11.29       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['139', '143'])).
% 11.10/11.29  thf('145', plain,
% 11.10/11.29      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 11.10/11.29       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('split', [status(esa)], ['137'])).
% 11.10/11.29  thf('146', plain,
% 11.10/11.29      (![X24 : $i]:
% 11.10/11.29         (((k3_yellow_0 @ X24) = (k1_yellow_0 @ X24 @ k1_xboole_0))
% 11.10/11.29          | ~ (l1_orders_2 @ X24))),
% 11.10/11.29      inference('cnf', [status(esa)], [d11_yellow_0])).
% 11.10/11.29  thf('147', plain,
% 11.10/11.29      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('148', plain,
% 11.10/11.29      (![X36 : $i, X37 : $i]:
% 11.10/11.29         (((X37) = (X36))
% 11.10/11.29          | (v1_subset_1 @ X37 @ X36)
% 11.10/11.29          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 11.10/11.29      inference('cnf', [status(esa)], [d7_subset_1])).
% 11.10/11.29  thf('149', plain,
% 11.10/11.29      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 11.10/11.29        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['147', '148'])).
% 11.10/11.29  thf('150', plain,
% 11.10/11.29      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('split', [status(esa)], ['0'])).
% 11.10/11.29  thf('151', plain,
% 11.10/11.29      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 11.10/11.29         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('sup-', [status(thm)], ['149', '150'])).
% 11.10/11.29  thf('152', plain,
% 11.10/11.29      (![X29 : $i, X30 : $i]:
% 11.10/11.29         (~ (l1_orders_2 @ X29)
% 11.10/11.29          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 11.10/11.29      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 11.10/11.29  thf('153', plain,
% 11.10/11.29      ((![X0 : $i]:
% 11.10/11.29          ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 11.10/11.29           | ~ (l1_orders_2 @ sk_A)))
% 11.10/11.29         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('sup+', [status(thm)], ['151', '152'])).
% 11.10/11.29  thf('154', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('155', plain,
% 11.10/11.29      ((![X0 : $i]: (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 11.10/11.29         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('demod', [status(thm)], ['153', '154'])).
% 11.10/11.29  thf('156', plain,
% 11.10/11.29      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1) | ~ (l1_orders_2 @ sk_A)))
% 11.10/11.29         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('sup+', [status(thm)], ['146', '155'])).
% 11.10/11.29  thf('157', plain, ((l1_orders_2 @ sk_A)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('158', plain,
% 11.10/11.29      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 11.10/11.29         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('demod', [status(thm)], ['156', '157'])).
% 11.10/11.29  thf('159', plain,
% 11.10/11.29      (![X12 : $i, X13 : $i]:
% 11.10/11.29         ((r2_hidden @ X12 @ X13)
% 11.10/11.29          | (v1_xboole_0 @ X13)
% 11.10/11.29          | ~ (m1_subset_1 @ X12 @ X13))),
% 11.10/11.29      inference('cnf', [status(esa)], [t2_subset])).
% 11.10/11.29  thf('160', plain,
% 11.10/11.29      ((((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 11.10/11.29         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('sup-', [status(thm)], ['158', '159'])).
% 11.10/11.29  thf('161', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 11.10/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.29  thf('162', plain,
% 11.10/11.29      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 11.10/11.29         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 11.10/11.29      inference('clc', [status(thm)], ['160', '161'])).
% 11.10/11.29  thf('163', plain,
% 11.10/11.29      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 11.10/11.29         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 11.10/11.29      inference('split', [status(esa)], ['137'])).
% 11.10/11.29  thf('164', plain,
% 11.10/11.29      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 11.10/11.29       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 11.10/11.29      inference('sup-', [status(thm)], ['162', '163'])).
% 11.10/11.29  thf('165', plain, ($false),
% 11.10/11.29      inference('sat_resolution*', [status(thm)], ['1', '144', '145', '164'])).
% 11.10/11.29  
% 11.10/11.29  % SZS output end Refutation
% 11.10/11.29  
% 11.10/11.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
