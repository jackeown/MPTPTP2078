%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UFgclpy1rx

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:13 EST 2020

% Result     : Theorem 4.14s
% Output     : Refutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 418 expanded)
%              Number of leaves         :   44 ( 137 expanded)
%              Depth                    :   26
%              Number of atoms          : 1736 (6370 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

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
    ! [X29: $i] :
      ( ( r1_yellow_0 @ X29 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v1_yellow_0 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('6',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('7',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

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

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( X6 = X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

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

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X19 @ X18 ) @ X19 )
      | ( r2_lattice3 @ X18 @ X19 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
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

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X24
       != ( k1_yellow_0 @ X22 @ X23 ) )
      | ~ ( r2_lattice3 @ X22 @ X23 @ X25 )
      | ( r1_orders_2 @ X22 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_yellow_0 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('25',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ~ ( r1_yellow_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ( r1_orders_2 @ X22 @ ( k1_yellow_0 @ X22 @ X23 ) @ X25 )
      | ~ ( r2_lattice3 @ X22 @ X23 @ X25 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','32'])).

thf('34',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X21: $i] :
      ( ( ( k3_yellow_0 @ X21 )
        = ( k1_yellow_0 @ X21 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('42',plain,(
    ! [X29: $i] :
      ( ( r1_yellow_0 @ X29 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v1_yellow_0 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X19 @ X18 ) @ X19 )
      | ( r2_lattice3 @ X18 @ X19 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k1_yellow_0 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D_1 @ ( k1_yellow_0 @ X1 @ X2 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('63',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r2_hidden @ X32 @ X30 )
      | ~ ( r1_orders_2 @ X31 @ X33 @ X32 )
      | ~ ( r2_hidden @ X33 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','76'])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('88',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('92',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('94',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('98',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( X6 = X4 )
      | ~ ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('102',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['95','102'])).

thf('104',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('105',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('111',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ X7 @ X7 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['106'])).

thf('114',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('116',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('119',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('120',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['106'])).

thf('129',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','112','113','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UFgclpy1rx
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.14/4.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.14/4.33  % Solved by: fo/fo7.sh
% 4.14/4.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.14/4.33  % done 3353 iterations in 3.884s
% 4.14/4.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.14/4.33  % SZS output start Refutation
% 4.14/4.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.14/4.33  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 4.14/4.33  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 4.14/4.33  thf(sk_A_type, type, sk_A: $i).
% 4.14/4.33  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 4.14/4.33  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.14/4.33  thf(sk_B_type, type, sk_B: $i > $i).
% 4.14/4.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.14/4.33  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 4.14/4.33  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 4.14/4.33  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.14/4.33  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 4.14/4.33  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 4.14/4.33  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 4.14/4.33  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 4.14/4.33  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 4.14/4.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.14/4.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.14/4.33  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.14/4.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.14/4.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.14/4.33  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 4.14/4.33  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 4.14/4.33  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 4.14/4.33  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.14/4.33  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 4.14/4.33  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 4.14/4.33  thf(t8_waybel_7, conjecture,
% 4.14/4.33    (![A:$i]:
% 4.14/4.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 4.14/4.33         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 4.14/4.33         ( l1_orders_2 @ A ) ) =>
% 4.14/4.33       ( ![B:$i]:
% 4.14/4.33         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 4.14/4.33             ( v13_waybel_0 @ B @ A ) & 
% 4.14/4.33             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.14/4.33           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 4.14/4.33             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 4.14/4.33  thf(zf_stmt_0, negated_conjecture,
% 4.14/4.33    (~( ![A:$i]:
% 4.14/4.33        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 4.14/4.33            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 4.14/4.33            ( l1_orders_2 @ A ) ) =>
% 4.14/4.33          ( ![B:$i]:
% 4.14/4.33            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 4.14/4.33                ( v13_waybel_0 @ B @ A ) & 
% 4.14/4.33                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.14/4.33              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 4.14/4.33                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 4.14/4.33    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 4.14/4.33  thf('0', plain,
% 4.14/4.33      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 4.14/4.33        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('1', plain,
% 4.14/4.33      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 4.14/4.33       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('split', [status(esa)], ['0'])).
% 4.14/4.33  thf(t42_yellow_0, axiom,
% 4.14/4.33    (![A:$i]:
% 4.14/4.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 4.14/4.33         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 4.14/4.33       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 4.14/4.33         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 4.14/4.33  thf('2', plain,
% 4.14/4.33      (![X29 : $i]:
% 4.14/4.33         ((r1_yellow_0 @ X29 @ k1_xboole_0)
% 4.14/4.33          | ~ (l1_orders_2 @ X29)
% 4.14/4.33          | ~ (v1_yellow_0 @ X29)
% 4.14/4.33          | ~ (v5_orders_2 @ X29)
% 4.14/4.33          | (v2_struct_0 @ X29))),
% 4.14/4.33      inference('cnf', [status(esa)], [t42_yellow_0])).
% 4.14/4.33  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.14/4.33  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.14/4.33      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.14/4.33  thf('4', plain,
% 4.14/4.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf(rc3_subset_1, axiom,
% 4.14/4.33    (![A:$i]:
% 4.14/4.33     ( ?[B:$i]:
% 4.14/4.33       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 4.14/4.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 4.14/4.33  thf('5', plain,
% 4.14/4.33      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 4.14/4.33      inference('cnf', [status(esa)], [rc3_subset_1])).
% 4.14/4.33  thf('6', plain,
% 4.14/4.33      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 4.14/4.33      inference('cnf', [status(esa)], [rc3_subset_1])).
% 4.14/4.33  thf(d7_subset_1, axiom,
% 4.14/4.33    (![A:$i,B:$i]:
% 4.14/4.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.14/4.33       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 4.14/4.33  thf('7', plain,
% 4.14/4.33      (![X34 : $i, X35 : $i]:
% 4.14/4.33         (((X35) = (X34))
% 4.14/4.33          | (v1_subset_1 @ X35 @ X34)
% 4.14/4.33          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 4.14/4.33      inference('cnf', [status(esa)], [d7_subset_1])).
% 4.14/4.33  thf('8', plain,
% 4.14/4.33      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['6', '7'])).
% 4.14/4.33  thf('9', plain, (![X7 : $i]: ~ (v1_subset_1 @ (sk_B @ X7) @ X7)),
% 4.14/4.33      inference('cnf', [status(esa)], [rc3_subset_1])).
% 4.14/4.33  thf('10', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 4.14/4.33      inference('clc', [status(thm)], ['8', '9'])).
% 4.14/4.33  thf('11', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 4.14/4.33      inference('demod', [status(thm)], ['5', '10'])).
% 4.14/4.33  thf(t8_subset_1, axiom,
% 4.14/4.33    (![A:$i,B:$i]:
% 4.14/4.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.14/4.33       ( ![C:$i]:
% 4.14/4.33         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.14/4.33           ( ( ![D:$i]:
% 4.14/4.33               ( ( m1_subset_1 @ D @ A ) =>
% 4.14/4.33                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 4.14/4.33             ( ( B ) = ( C ) ) ) ) ) ))).
% 4.14/4.33  thf('12', plain,
% 4.14/4.33      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 4.14/4.33          | ((X6) = (X4))
% 4.14/4.33          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ X5)
% 4.14/4.33          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 4.14/4.33      inference('cnf', [status(esa)], [t8_subset_1])).
% 4.14/4.33  thf('13', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 4.14/4.33          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.14/4.33          | ((X1) = (X0)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['11', '12'])).
% 4.14/4.33  thf('14', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33        | (m1_subset_1 @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33           (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['4', '13'])).
% 4.14/4.33  thf(d9_lattice3, axiom,
% 4.14/4.33    (![A:$i]:
% 4.14/4.33     ( ( l1_orders_2 @ A ) =>
% 4.14/4.33       ( ![B:$i,C:$i]:
% 4.14/4.33         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.14/4.33           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 4.14/4.33             ( ![D:$i]:
% 4.14/4.33               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.14/4.33                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 4.14/4.33  thf('15', plain,
% 4.14/4.33      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 4.14/4.33          | (r2_hidden @ (sk_D_1 @ X17 @ X19 @ X18) @ X19)
% 4.14/4.33          | (r2_lattice3 @ X18 @ X19 @ X17)
% 4.14/4.33          | ~ (l1_orders_2 @ X18))),
% 4.14/4.33      inference('cnf', [status(esa)], [d9_lattice3])).
% 4.14/4.33  thf('16', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (l1_orders_2 @ sk_A)
% 4.14/4.33          | (r2_lattice3 @ sk_A @ X0 @ 
% 4.14/4.33             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33          | (r2_hidden @ 
% 4.14/4.33             (sk_D_1 @ 
% 4.14/4.33              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33              X0 @ sk_A) @ 
% 4.14/4.33             X0))),
% 4.14/4.33      inference('sup-', [status(thm)], ['14', '15'])).
% 4.14/4.33  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('18', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33          | (r2_lattice3 @ sk_A @ X0 @ 
% 4.14/4.33             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33          | (r2_hidden @ 
% 4.14/4.33             (sk_D_1 @ 
% 4.14/4.33              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33              X0 @ sk_A) @ 
% 4.14/4.33             X0))),
% 4.14/4.33      inference('demod', [status(thm)], ['16', '17'])).
% 4.14/4.33  thf(t7_ordinal1, axiom,
% 4.14/4.33    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.14/4.33  thf('19', plain,
% 4.14/4.33      (![X15 : $i, X16 : $i]:
% 4.14/4.33         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 4.14/4.33      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.14/4.33  thf('20', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         ((r2_lattice3 @ sk_A @ X0 @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33          | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (r1_tarski @ X0 @ 
% 4.14/4.33               (sk_D_1 @ 
% 4.14/4.33                (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33                X0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['18', '19'])).
% 4.14/4.33  thf('21', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('sup-', [status(thm)], ['3', '20'])).
% 4.14/4.33  thf('22', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33        | (m1_subset_1 @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33           (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['4', '13'])).
% 4.14/4.33  thf(dt_k1_yellow_0, axiom,
% 4.14/4.33    (![A:$i,B:$i]:
% 4.14/4.33     ( ( l1_orders_2 @ A ) =>
% 4.14/4.33       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 4.14/4.33  thf('23', plain,
% 4.14/4.33      (![X26 : $i, X27 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X26)
% 4.14/4.33          | (m1_subset_1 @ (k1_yellow_0 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 4.14/4.33      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 4.14/4.33  thf(d9_yellow_0, axiom,
% 4.14/4.33    (![A:$i]:
% 4.14/4.33     ( ( l1_orders_2 @ A ) =>
% 4.14/4.33       ( ![B:$i,C:$i]:
% 4.14/4.33         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.14/4.33           ( ( r1_yellow_0 @ A @ B ) =>
% 4.14/4.33             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 4.14/4.33               ( ( r2_lattice3 @ A @ B @ C ) & 
% 4.14/4.33                 ( ![D:$i]:
% 4.14/4.33                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.14/4.33                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 4.14/4.33                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 4.14/4.33  thf('24', plain,
% 4.14/4.33      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 4.14/4.33         (((X24) != (k1_yellow_0 @ X22 @ X23))
% 4.14/4.33          | ~ (r2_lattice3 @ X22 @ X23 @ X25)
% 4.14/4.33          | (r1_orders_2 @ X22 @ X24 @ X25)
% 4.14/4.33          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 4.14/4.33          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 4.14/4.33          | ~ (r1_yellow_0 @ X22 @ X23)
% 4.14/4.33          | ~ (l1_orders_2 @ X22))),
% 4.14/4.33      inference('cnf', [status(esa)], [d9_yellow_0])).
% 4.14/4.33  thf('25', plain,
% 4.14/4.33      (![X22 : $i, X23 : $i, X25 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X22)
% 4.14/4.33          | ~ (r1_yellow_0 @ X22 @ X23)
% 4.14/4.33          | ~ (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22))
% 4.14/4.33          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 4.14/4.33          | (r1_orders_2 @ X22 @ (k1_yellow_0 @ X22 @ X23) @ X25)
% 4.14/4.33          | ~ (r2_lattice3 @ X22 @ X23 @ X25))),
% 4.14/4.33      inference('simplify', [status(thm)], ['24'])).
% 4.14/4.33  thf('26', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X0)
% 4.14/4.33          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 4.14/4.33          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 4.14/4.33          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.14/4.33          | ~ (r1_yellow_0 @ X0 @ X1)
% 4.14/4.33          | ~ (l1_orders_2 @ X0))),
% 4.14/4.33      inference('sup-', [status(thm)], ['23', '25'])).
% 4.14/4.33  thf('27', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         (~ (r1_yellow_0 @ X0 @ X1)
% 4.14/4.33          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.14/4.33          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 4.14/4.33          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 4.14/4.33          | ~ (l1_orders_2 @ X0))),
% 4.14/4.33      inference('simplify', [status(thm)], ['26'])).
% 4.14/4.33  thf('28', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (l1_orders_2 @ sk_A)
% 4.14/4.33          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 4.14/4.33               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 4.14/4.33             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 4.14/4.33      inference('sup-', [status(thm)], ['22', '27'])).
% 4.14/4.33  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('30', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 4.14/4.33               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 4.14/4.33             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 4.14/4.33      inference('demod', [status(thm)], ['28', '29'])).
% 4.14/4.33  thf('31', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 4.14/4.33        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['21', '30'])).
% 4.14/4.33  thf('32', plain,
% 4.14/4.33      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 4.14/4.33         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 4.14/4.33        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('simplify', [status(thm)], ['31'])).
% 4.14/4.33  thf('33', plain,
% 4.14/4.33      (((v2_struct_0 @ sk_A)
% 4.14/4.33        | ~ (v5_orders_2 @ sk_A)
% 4.14/4.33        | ~ (v1_yellow_0 @ sk_A)
% 4.14/4.33        | ~ (l1_orders_2 @ sk_A)
% 4.14/4.33        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('sup-', [status(thm)], ['2', '32'])).
% 4.14/4.33  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('35', plain, ((v1_yellow_0 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('37', plain,
% 4.14/4.33      (((v2_struct_0 @ sk_A)
% 4.14/4.33        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 4.14/4.33  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('39', plain,
% 4.14/4.33      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 4.14/4.33         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('clc', [status(thm)], ['37', '38'])).
% 4.14/4.33  thf('40', plain,
% 4.14/4.33      (![X26 : $i, X27 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X26)
% 4.14/4.33          | (m1_subset_1 @ (k1_yellow_0 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 4.14/4.33      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 4.14/4.33  thf(d11_yellow_0, axiom,
% 4.14/4.33    (![A:$i]:
% 4.14/4.33     ( ( l1_orders_2 @ A ) =>
% 4.14/4.33       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 4.14/4.33  thf('41', plain,
% 4.14/4.33      (![X21 : $i]:
% 4.14/4.33         (((k3_yellow_0 @ X21) = (k1_yellow_0 @ X21 @ k1_xboole_0))
% 4.14/4.33          | ~ (l1_orders_2 @ X21))),
% 4.14/4.33      inference('cnf', [status(esa)], [d11_yellow_0])).
% 4.14/4.33  thf('42', plain,
% 4.14/4.33      (![X29 : $i]:
% 4.14/4.33         ((r1_yellow_0 @ X29 @ k1_xboole_0)
% 4.14/4.33          | ~ (l1_orders_2 @ X29)
% 4.14/4.33          | ~ (v1_yellow_0 @ X29)
% 4.14/4.33          | ~ (v5_orders_2 @ X29)
% 4.14/4.33          | (v2_struct_0 @ X29))),
% 4.14/4.33      inference('cnf', [status(esa)], [t42_yellow_0])).
% 4.14/4.33  thf('43', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.14/4.33      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.14/4.33  thf('44', plain,
% 4.14/4.33      (![X26 : $i, X27 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X26)
% 4.14/4.33          | (m1_subset_1 @ (k1_yellow_0 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 4.14/4.33      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 4.14/4.33  thf('45', plain,
% 4.14/4.33      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 4.14/4.33          | (r2_hidden @ (sk_D_1 @ X17 @ X19 @ X18) @ X19)
% 4.14/4.33          | (r2_lattice3 @ X18 @ X19 @ X17)
% 4.14/4.33          | ~ (l1_orders_2 @ X18))),
% 4.14/4.33      inference('cnf', [status(esa)], [d9_lattice3])).
% 4.14/4.33  thf('46', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X0)
% 4.14/4.33          | ~ (l1_orders_2 @ X0)
% 4.14/4.33          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | (r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2))),
% 4.14/4.33      inference('sup-', [status(thm)], ['44', '45'])).
% 4.14/4.33  thf('47', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         ((r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2)
% 4.14/4.33          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | ~ (l1_orders_2 @ X0))),
% 4.14/4.33      inference('simplify', [status(thm)], ['46'])).
% 4.14/4.33  thf('48', plain,
% 4.14/4.33      (![X15 : $i, X16 : $i]:
% 4.14/4.33         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 4.14/4.33      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.14/4.33  thf('49', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X1)
% 4.14/4.33          | (r2_lattice3 @ X1 @ X0 @ (k1_yellow_0 @ X1 @ X2))
% 4.14/4.33          | ~ (r1_tarski @ X0 @ (sk_D_1 @ (k1_yellow_0 @ X1 @ X2) @ X0 @ X1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['47', '48'])).
% 4.14/4.33  thf('50', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | ~ (l1_orders_2 @ X0))),
% 4.14/4.33      inference('sup-', [status(thm)], ['43', '49'])).
% 4.14/4.33  thf('51', plain,
% 4.14/4.33      (![X26 : $i, X27 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X26)
% 4.14/4.33          | (m1_subset_1 @ (k1_yellow_0 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 4.14/4.33      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 4.14/4.33  thf('52', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         (~ (r1_yellow_0 @ X0 @ X1)
% 4.14/4.33          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.14/4.33          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 4.14/4.33          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 4.14/4.33          | ~ (l1_orders_2 @ X0))),
% 4.14/4.33      inference('simplify', [status(thm)], ['26'])).
% 4.14/4.33  thf('53', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X0)
% 4.14/4.33          | ~ (l1_orders_2 @ X0)
% 4.14/4.33          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 4.14/4.33             (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | ~ (r1_yellow_0 @ X0 @ X2))),
% 4.14/4.33      inference('sup-', [status(thm)], ['51', '52'])).
% 4.14/4.33  thf('54', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.14/4.33         (~ (r1_yellow_0 @ X0 @ X2)
% 4.14/4.33          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 4.14/4.33             (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | ~ (l1_orders_2 @ X0))),
% 4.14/4.33      inference('simplify', [status(thm)], ['53'])).
% 4.14/4.33  thf('55', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X1)
% 4.14/4.33          | ~ (l1_orders_2 @ X1)
% 4.14/4.33          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 4.14/4.33             (k1_yellow_0 @ X1 @ X0))
% 4.14/4.33          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0))),
% 4.14/4.33      inference('sup-', [status(thm)], ['50', '54'])).
% 4.14/4.33  thf('56', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 4.14/4.33          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 4.14/4.33             (k1_yellow_0 @ X1 @ X0))
% 4.14/4.33          | ~ (l1_orders_2 @ X1))),
% 4.14/4.33      inference('simplify', [status(thm)], ['55'])).
% 4.14/4.33  thf('57', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         ((v2_struct_0 @ X0)
% 4.14/4.33          | ~ (v5_orders_2 @ X0)
% 4.14/4.33          | ~ (v1_yellow_0 @ X0)
% 4.14/4.33          | ~ (l1_orders_2 @ X0)
% 4.14/4.33          | ~ (l1_orders_2 @ X0)
% 4.14/4.33          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 4.14/4.33             (k1_yellow_0 @ X0 @ X1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['42', '56'])).
% 4.14/4.33  thf('58', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 4.14/4.33           (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | ~ (l1_orders_2 @ X0)
% 4.14/4.33          | ~ (v1_yellow_0 @ X0)
% 4.14/4.33          | ~ (v5_orders_2 @ X0)
% 4.14/4.33          | (v2_struct_0 @ X0))),
% 4.14/4.33      inference('simplify', [status(thm)], ['57'])).
% 4.14/4.33  thf('59', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 4.14/4.33          | ~ (l1_orders_2 @ X0)
% 4.14/4.33          | (v2_struct_0 @ X0)
% 4.14/4.33          | ~ (v5_orders_2 @ X0)
% 4.14/4.33          | ~ (v1_yellow_0 @ X0)
% 4.14/4.33          | ~ (l1_orders_2 @ X0))),
% 4.14/4.33      inference('sup+', [status(thm)], ['41', '58'])).
% 4.14/4.33  thf('60', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (~ (v1_yellow_0 @ X0)
% 4.14/4.33          | ~ (v5_orders_2 @ X0)
% 4.14/4.33          | (v2_struct_0 @ X0)
% 4.14/4.33          | ~ (l1_orders_2 @ X0)
% 4.14/4.33          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 4.14/4.33      inference('simplify', [status(thm)], ['59'])).
% 4.14/4.33  thf('61', plain,
% 4.14/4.33      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('split', [status(esa)], ['0'])).
% 4.14/4.33  thf('62', plain,
% 4.14/4.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf(l3_subset_1, axiom,
% 4.14/4.33    (![A:$i,B:$i]:
% 4.14/4.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.14/4.33       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 4.14/4.33  thf('63', plain,
% 4.14/4.33      (![X1 : $i, X2 : $i, X3 : $i]:
% 4.14/4.33         (~ (r2_hidden @ X1 @ X2)
% 4.14/4.33          | (r2_hidden @ X1 @ X3)
% 4.14/4.33          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 4.14/4.33      inference('cnf', [status(esa)], [l3_subset_1])).
% 4.14/4.33  thf('64', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 4.14/4.33      inference('sup-', [status(thm)], ['62', '63'])).
% 4.14/4.33  thf('65', plain,
% 4.14/4.33      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['61', '64'])).
% 4.14/4.33  thf(t1_subset, axiom,
% 4.14/4.33    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 4.14/4.33  thf('66', plain,
% 4.14/4.33      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 4.14/4.33      inference('cnf', [status(esa)], [t1_subset])).
% 4.14/4.33  thf('67', plain,
% 4.14/4.33      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['65', '66'])).
% 4.14/4.33  thf('68', plain,
% 4.14/4.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf(d20_waybel_0, axiom,
% 4.14/4.33    (![A:$i]:
% 4.14/4.33     ( ( l1_orders_2 @ A ) =>
% 4.14/4.33       ( ![B:$i]:
% 4.14/4.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.14/4.33           ( ( v13_waybel_0 @ B @ A ) <=>
% 4.14/4.33             ( ![C:$i]:
% 4.14/4.33               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.14/4.33                 ( ![D:$i]:
% 4.14/4.33                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.14/4.33                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 4.14/4.33                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 4.14/4.33  thf('69', plain,
% 4.14/4.33      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 4.14/4.33          | ~ (v13_waybel_0 @ X30 @ X31)
% 4.14/4.33          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 4.14/4.33          | (r2_hidden @ X32 @ X30)
% 4.14/4.33          | ~ (r1_orders_2 @ X31 @ X33 @ X32)
% 4.14/4.33          | ~ (r2_hidden @ X33 @ X30)
% 4.14/4.33          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 4.14/4.33          | ~ (l1_orders_2 @ X31))),
% 4.14/4.33      inference('cnf', [status(esa)], [d20_waybel_0])).
% 4.14/4.33  thf('70', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ sk_A)
% 4.14/4.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (r2_hidden @ X0 @ sk_B_1)
% 4.14/4.33          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 4.14/4.33          | (r2_hidden @ X1 @ sk_B_1)
% 4.14/4.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 4.14/4.33      inference('sup-', [status(thm)], ['68', '69'])).
% 4.14/4.33  thf('71', plain, ((l1_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('72', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('73', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (r2_hidden @ X0 @ sk_B_1)
% 4.14/4.33          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 4.14/4.33          | (r2_hidden @ X1 @ sk_B_1)
% 4.14/4.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('demod', [status(thm)], ['70', '71', '72'])).
% 4.14/4.33  thf('74', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.14/4.33           | (r2_hidden @ X0 @ sk_B_1)
% 4.14/4.33           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 4.14/4.33           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['67', '73'])).
% 4.14/4.33  thf('75', plain,
% 4.14/4.33      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('split', [status(esa)], ['0'])).
% 4.14/4.33  thf('76', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.14/4.33           | (r2_hidden @ X0 @ sk_B_1)
% 4.14/4.33           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('demod', [status(thm)], ['74', '75'])).
% 4.14/4.33  thf('77', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          (~ (l1_orders_2 @ sk_A)
% 4.14/4.33           | (v2_struct_0 @ sk_A)
% 4.14/4.33           | ~ (v5_orders_2 @ sk_A)
% 4.14/4.33           | ~ (v1_yellow_0 @ sk_A)
% 4.14/4.33           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 4.14/4.33           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['60', '76'])).
% 4.14/4.33  thf('78', plain, ((l1_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('79', plain, ((v5_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('80', plain, ((v1_yellow_0 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('81', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          ((v2_struct_0 @ sk_A)
% 4.14/4.33           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 4.14/4.33           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 4.14/4.33  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('83', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          (~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 4.14/4.33           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('clc', [status(thm)], ['81', '82'])).
% 4.14/4.33  thf('84', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          (~ (l1_orders_2 @ sk_A)
% 4.14/4.33           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['40', '83'])).
% 4.14/4.33  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('86', plain,
% 4.14/4.33      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('demod', [status(thm)], ['84', '85'])).
% 4.14/4.33  thf('87', plain,
% 4.14/4.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf(t4_subset, axiom,
% 4.14/4.33    (![A:$i,B:$i,C:$i]:
% 4.14/4.33     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 4.14/4.33       ( m1_subset_1 @ A @ C ) ))).
% 4.14/4.33  thf('88', plain,
% 4.14/4.33      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.14/4.33         (~ (r2_hidden @ X12 @ X13)
% 4.14/4.33          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.14/4.33          | (m1_subset_1 @ X12 @ X14))),
% 4.14/4.33      inference('cnf', [status(esa)], [t4_subset])).
% 4.14/4.33  thf('89', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 4.14/4.33      inference('sup-', [status(thm)], ['87', '88'])).
% 4.14/4.33  thf('90', plain,
% 4.14/4.33      ((![X0 : $i]:
% 4.14/4.33          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['86', '89'])).
% 4.14/4.33  thf('91', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.14/4.33          | ~ (r2_hidden @ X0 @ sk_B_1)
% 4.14/4.33          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 4.14/4.33          | (r2_hidden @ X1 @ sk_B_1)
% 4.14/4.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('demod', [status(thm)], ['70', '71', '72'])).
% 4.14/4.33  thf('92', plain,
% 4.14/4.33      ((![X0 : $i, X1 : $i]:
% 4.14/4.33          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 4.14/4.33           | (r2_hidden @ X1 @ sk_B_1)
% 4.14/4.33           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 4.14/4.33           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['90', '91'])).
% 4.14/4.33  thf('93', plain,
% 4.14/4.33      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('demod', [status(thm)], ['84', '85'])).
% 4.14/4.33  thf('94', plain,
% 4.14/4.33      ((![X0 : $i, X1 : $i]:
% 4.14/4.33          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 4.14/4.33           | (r2_hidden @ X1 @ sk_B_1)
% 4.14/4.33           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('demod', [status(thm)], ['92', '93'])).
% 4.14/4.33  thf('95', plain,
% 4.14/4.33      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33         | (r2_hidden @ 
% 4.14/4.33            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33            sk_B_1)
% 4.14/4.33         | ~ (m1_subset_1 @ 
% 4.14/4.33              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33              (u1_struct_0 @ sk_A))))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['39', '94'])).
% 4.14/4.33  thf('96', plain,
% 4.14/4.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('97', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 4.14/4.33      inference('demod', [status(thm)], ['5', '10'])).
% 4.14/4.33  thf('98', plain,
% 4.14/4.33      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 4.14/4.33          | ((X6) = (X4))
% 4.14/4.33          | ~ (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 4.14/4.33          | ~ (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X4)
% 4.14/4.33          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 4.14/4.33      inference('cnf', [status(esa)], [t8_subset_1])).
% 4.14/4.33  thf('99', plain,
% 4.14/4.33      (![X0 : $i, X1 : $i]:
% 4.14/4.33         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 4.14/4.33          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.14/4.33          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 4.14/4.33          | ((X1) = (X0)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['97', '98'])).
% 4.14/4.33  thf('100', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33        | ~ (r2_hidden @ 
% 4.14/4.33             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33             sk_B_1)
% 4.14/4.33        | ~ (r2_hidden @ 
% 4.14/4.33             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33             (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['96', '99'])).
% 4.14/4.33  thf('101', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 4.14/4.33      inference('sup-', [status(thm)], ['62', '63'])).
% 4.14/4.33  thf('102', plain,
% 4.14/4.33      ((~ (r2_hidden @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33           sk_B_1)
% 4.14/4.33        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('clc', [status(thm)], ['100', '101'])).
% 4.14/4.33  thf('103', plain,
% 4.14/4.33      (((~ (m1_subset_1 @ 
% 4.14/4.33            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33            (u1_struct_0 @ sk_A))
% 4.14/4.33         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('clc', [status(thm)], ['95', '102'])).
% 4.14/4.33  thf('104', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 4.14/4.33        | (m1_subset_1 @ 
% 4.14/4.33           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 4.14/4.33           (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['4', '13'])).
% 4.14/4.33  thf('105', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('clc', [status(thm)], ['103', '104'])).
% 4.14/4.33  thf('106', plain,
% 4.14/4.33      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 4.14/4.33        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('107', plain,
% 4.14/4.33      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('split', [status(esa)], ['106'])).
% 4.14/4.33  thf('108', plain,
% 4.14/4.33      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 4.14/4.33         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 4.14/4.33             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('sup+', [status(thm)], ['105', '107'])).
% 4.14/4.33  thf('109', plain, (![X7 : $i]: ~ (v1_subset_1 @ (sk_B @ X7) @ X7)),
% 4.14/4.33      inference('cnf', [status(esa)], [rc3_subset_1])).
% 4.14/4.33  thf('110', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 4.14/4.33      inference('clc', [status(thm)], ['8', '9'])).
% 4.14/4.33  thf('111', plain, (![X7 : $i]: ~ (v1_subset_1 @ X7 @ X7)),
% 4.14/4.33      inference('demod', [status(thm)], ['109', '110'])).
% 4.14/4.33  thf('112', plain,
% 4.14/4.33      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 4.14/4.33       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['108', '111'])).
% 4.14/4.33  thf('113', plain,
% 4.14/4.33      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 4.14/4.33       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('split', [status(esa)], ['106'])).
% 4.14/4.33  thf('114', plain,
% 4.14/4.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('115', plain,
% 4.14/4.33      (![X34 : $i, X35 : $i]:
% 4.14/4.33         (((X35) = (X34))
% 4.14/4.33          | (v1_subset_1 @ X35 @ X34)
% 4.14/4.33          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 4.14/4.33      inference('cnf', [status(esa)], [d7_subset_1])).
% 4.14/4.33  thf('116', plain,
% 4.14/4.33      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 4.14/4.33        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['114', '115'])).
% 4.14/4.33  thf('117', plain,
% 4.14/4.33      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('split', [status(esa)], ['0'])).
% 4.14/4.33  thf('118', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('sup-', [status(thm)], ['116', '117'])).
% 4.14/4.33  thf(dt_k3_yellow_0, axiom,
% 4.14/4.33    (![A:$i]:
% 4.14/4.33     ( ( l1_orders_2 @ A ) =>
% 4.14/4.33       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 4.14/4.33  thf('119', plain,
% 4.14/4.33      (![X28 : $i]:
% 4.14/4.33         ((m1_subset_1 @ (k3_yellow_0 @ X28) @ (u1_struct_0 @ X28))
% 4.14/4.33          | ~ (l1_orders_2 @ X28))),
% 4.14/4.33      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 4.14/4.33  thf(t2_subset, axiom,
% 4.14/4.33    (![A:$i,B:$i]:
% 4.14/4.33     ( ( m1_subset_1 @ A @ B ) =>
% 4.14/4.33       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 4.14/4.33  thf('120', plain,
% 4.14/4.33      (![X10 : $i, X11 : $i]:
% 4.14/4.33         ((r2_hidden @ X10 @ X11)
% 4.14/4.33          | (v1_xboole_0 @ X11)
% 4.14/4.33          | ~ (m1_subset_1 @ X10 @ X11))),
% 4.14/4.33      inference('cnf', [status(esa)], [t2_subset])).
% 4.14/4.33  thf('121', plain,
% 4.14/4.33      (![X0 : $i]:
% 4.14/4.33         (~ (l1_orders_2 @ X0)
% 4.14/4.33          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 4.14/4.33          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['119', '120'])).
% 4.14/4.33  thf('122', plain,
% 4.14/4.33      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 4.14/4.33         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 4.14/4.33         | ~ (l1_orders_2 @ sk_A)))
% 4.14/4.33         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('sup+', [status(thm)], ['118', '121'])).
% 4.14/4.33  thf('123', plain,
% 4.14/4.33      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 4.14/4.33         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('sup-', [status(thm)], ['116', '117'])).
% 4.14/4.33  thf('124', plain, ((l1_orders_2 @ sk_A)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('125', plain,
% 4.14/4.33      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 4.14/4.33         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('demod', [status(thm)], ['122', '123', '124'])).
% 4.14/4.33  thf('126', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 4.14/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.14/4.33  thf('127', plain,
% 4.14/4.33      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 4.14/4.33         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 4.14/4.33      inference('clc', [status(thm)], ['125', '126'])).
% 4.14/4.33  thf('128', plain,
% 4.14/4.33      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 4.14/4.33         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 4.14/4.33      inference('split', [status(esa)], ['106'])).
% 4.14/4.33  thf('129', plain,
% 4.14/4.33      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 4.14/4.33       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 4.14/4.33      inference('sup-', [status(thm)], ['127', '128'])).
% 4.14/4.33  thf('130', plain, ($false),
% 4.14/4.33      inference('sat_resolution*', [status(thm)], ['1', '112', '113', '129'])).
% 4.14/4.33  
% 4.14/4.33  % SZS output end Refutation
% 4.14/4.33  
% 4.14/4.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
