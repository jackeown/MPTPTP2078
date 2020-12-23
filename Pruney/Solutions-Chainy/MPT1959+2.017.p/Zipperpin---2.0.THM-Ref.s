%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sLOb5pDiZM

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:11 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 668 expanded)
%              Number of leaves         :   44 ( 210 expanded)
%              Depth                    :   36
%              Number of atoms          : 2149 (9989 expanded)
%              Number of equality atoms :   36 (  94 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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
    ! [X24: $i] :
      ( ( r1_yellow_0 @ X24 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( X10 = X8 )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X10 @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r2_lattice3 @ X26 @ k1_xboole_0 @ X25 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('11',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
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

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X20
       != ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( r2_lattice3 @ X18 @ X19 @ X21 )
      | ( r1_orders_2 @ X18 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('17',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( r1_orders_2 @ X18 @ ( k1_yellow_0 @ X18 @ X19 ) @ X21 )
      | ~ ( r2_lattice3 @ X18 @ X19 @ X21 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('34',plain,(
    ! [X24: $i] :
      ( ( r1_yellow_0 @ X24 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r2_lattice3 @ X26 @ k1_xboole_0 @ X25 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ ( sk_C @ X27 @ X28 ) @ X27 )
      | ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('55',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('60',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ X27 @ X28 ) @ X27 )
      | ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_2 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['53','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('71',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( r1_orders_2 @ X28 @ X30 @ X29 )
      | ~ ( r2_hidden @ X30 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('76',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','80'])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','90'])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('95',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( r1_orders_2 @ X28 @ X30 @ X29 )
      | ~ ( r2_hidden @ X30 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('106',plain,(
    ! [X24: $i] :
      ( ( r1_yellow_0 @ X24 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('107',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('108',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r2_lattice3 @ X26 @ k1_xboole_0 @ X25 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ! [X0: $i] :
        ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k1_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['106','115'])).

thf('117',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ! [X0: $i] :
        ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['105','122'])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ! [X0: $i] :
        ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['125','130'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['104','133'])).

thf('135',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('138',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( X10 = X8 )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('142',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['135','142'])).

thf('144',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('145',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['146'])).

thf('148',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['145','147'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('149',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('150',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('151',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ X11 @ X11 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['146'])).

thf('154',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('155',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('156',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 = X31 )
      | ( v1_subset_1 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('157',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('159',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('161',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['154','163'])).

thf('165',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('168',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['146'])).

thf('172',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','152','153','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sLOb5pDiZM
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.86/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.86/1.05  % Solved by: fo/fo7.sh
% 0.86/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.05  % done 1180 iterations in 0.598s
% 0.86/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.86/1.05  % SZS output start Refutation
% 0.86/1.05  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.86/1.05  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.86/1.05  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.86/1.05  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.86/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.86/1.05  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.86/1.05  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.86/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.86/1.05  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.86/1.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.86/1.05  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.86/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.86/1.05  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.86/1.05  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.86/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.05  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.86/1.05  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.86/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.86/1.05  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.86/1.05  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.86/1.05  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.86/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.86/1.05  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.86/1.05  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.86/1.05  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.86/1.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.86/1.05  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.86/1.05  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.86/1.05  thf(t8_waybel_7, conjecture,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.86/1.05         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.86/1.05         ( l1_orders_2 @ A ) ) =>
% 0.86/1.05       ( ![B:$i]:
% 0.86/1.05         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.86/1.05             ( v13_waybel_0 @ B @ A ) & 
% 0.86/1.05             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.86/1.05           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.86/1.05             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.86/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.05    (~( ![A:$i]:
% 0.86/1.05        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.86/1.05            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.86/1.05            ( l1_orders_2 @ A ) ) =>
% 0.86/1.05          ( ![B:$i]:
% 0.86/1.05            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.86/1.05                ( v13_waybel_0 @ B @ A ) & 
% 0.86/1.05                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.86/1.05              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.86/1.05                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.86/1.05    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.86/1.05  thf('0', plain,
% 0.86/1.05      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.86/1.05        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('1', plain,
% 0.86/1.05      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.86/1.05       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('split', [status(esa)], ['0'])).
% 0.86/1.05  thf(t42_yellow_0, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.86/1.05         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.86/1.05       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.86/1.05         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.86/1.05  thf('2', plain,
% 0.86/1.05      (![X24 : $i]:
% 0.86/1.05         ((r1_yellow_0 @ X24 @ k1_xboole_0)
% 0.86/1.05          | ~ (l1_orders_2 @ X24)
% 0.86/1.05          | ~ (v1_yellow_0 @ X24)
% 0.86/1.05          | ~ (v5_orders_2 @ X24)
% 0.86/1.05          | (v2_struct_0 @ X24))),
% 0.86/1.05      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.86/1.05  thf('3', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf(dt_k2_subset_1, axiom,
% 0.86/1.05    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.86/1.05  thf('4', plain,
% 0.86/1.05      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.86/1.05      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.86/1.05  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.86/1.05  thf('5', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.86/1.05      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.86/1.05  thf('6', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.86/1.05      inference('demod', [status(thm)], ['4', '5'])).
% 0.86/1.05  thf(t8_subset_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.86/1.05       ( ![C:$i]:
% 0.86/1.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.86/1.05           ( ( ![D:$i]:
% 0.86/1.05               ( ( m1_subset_1 @ D @ A ) =>
% 0.86/1.05                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.86/1.05             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.86/1.05  thf('7', plain,
% 0.86/1.05      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.86/1.05          | ((X10) = (X8))
% 0.86/1.05          | (m1_subset_1 @ (sk_D @ X8 @ X10 @ X9) @ X9)
% 0.86/1.05          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.86/1.05  thf('8', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.86/1.05          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.86/1.05          | ((X1) = (X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['6', '7'])).
% 0.86/1.05  thf('9', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | (m1_subset_1 @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05           (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['3', '8'])).
% 0.86/1.05  thf(t6_yellow_0, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( l1_orders_2 @ A ) =>
% 0.86/1.05       ( ![B:$i]:
% 0.86/1.05         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.86/1.05           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.86/1.05             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.86/1.05  thf('10', plain,
% 0.86/1.05      (![X25 : $i, X26 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.86/1.05          | (r2_lattice3 @ X26 @ k1_xboole_0 @ X25)
% 0.86/1.05          | ~ (l1_orders_2 @ X26))),
% 0.86/1.05      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.86/1.05  thf('11', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | ~ (l1_orders_2 @ sk_A)
% 0.86/1.05        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['9', '10'])).
% 0.86/1.05  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('13', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('demod', [status(thm)], ['11', '12'])).
% 0.86/1.05  thf('14', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | (m1_subset_1 @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05           (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['3', '8'])).
% 0.86/1.05  thf(dt_k1_yellow_0, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( l1_orders_2 @ A ) =>
% 0.86/1.05       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.86/1.05  thf('15', plain,
% 0.86/1.05      (![X22 : $i, X23 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X22)
% 0.86/1.05          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.86/1.05      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.86/1.05  thf(d9_yellow_0, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( l1_orders_2 @ A ) =>
% 0.86/1.05       ( ![B:$i,C:$i]:
% 0.86/1.05         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.86/1.05           ( ( r1_yellow_0 @ A @ B ) =>
% 0.86/1.05             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.86/1.05               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.86/1.05                 ( ![D:$i]:
% 0.86/1.05                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.86/1.05                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.86/1.05                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.86/1.05  thf('16', plain,
% 0.86/1.05      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.86/1.05         (((X20) != (k1_yellow_0 @ X18 @ X19))
% 0.86/1.05          | ~ (r2_lattice3 @ X18 @ X19 @ X21)
% 0.86/1.05          | (r1_orders_2 @ X18 @ X20 @ X21)
% 0.86/1.05          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.86/1.05          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.86/1.05          | ~ (r1_yellow_0 @ X18 @ X19)
% 0.86/1.05          | ~ (l1_orders_2 @ X18))),
% 0.86/1.05      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.86/1.05  thf('17', plain,
% 0.86/1.05      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X18)
% 0.86/1.05          | ~ (r1_yellow_0 @ X18 @ X19)
% 0.86/1.05          | ~ (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18))
% 0.86/1.05          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.86/1.05          | (r1_orders_2 @ X18 @ (k1_yellow_0 @ X18 @ X19) @ X21)
% 0.86/1.05          | ~ (r2_lattice3 @ X18 @ X19 @ X21))),
% 0.86/1.05      inference('simplify', [status(thm)], ['16'])).
% 0.86/1.05  thf('18', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X0)
% 0.86/1.05          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.86/1.05          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.86/1.05          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.86/1.05          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.86/1.05          | ~ (l1_orders_2 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['15', '17'])).
% 0.86/1.05  thf('19', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.05         (~ (r1_yellow_0 @ X0 @ X1)
% 0.86/1.05          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.86/1.05          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.86/1.05          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.86/1.05          | ~ (l1_orders_2 @ X0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['18'])).
% 0.86/1.05  thf('20', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05          | ~ (l1_orders_2 @ sk_A)
% 0.86/1.05          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.86/1.05               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.86/1.05             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['14', '19'])).
% 0.86/1.05  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('22', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.86/1.05               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.86/1.05             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.86/1.05      inference('demod', [status(thm)], ['20', '21'])).
% 0.86/1.05  thf('23', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.86/1.05        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['13', '22'])).
% 0.86/1.05  thf('24', plain,
% 0.86/1.05      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.86/1.05        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('simplify', [status(thm)], ['23'])).
% 0.86/1.05  thf('25', plain,
% 0.86/1.05      (((v2_struct_0 @ sk_A)
% 0.86/1.05        | ~ (v5_orders_2 @ sk_A)
% 0.86/1.05        | ~ (v1_yellow_0 @ sk_A)
% 0.86/1.05        | ~ (l1_orders_2 @ sk_A)
% 0.86/1.05        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['2', '24'])).
% 0.86/1.05  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('27', plain, ((v1_yellow_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('29', plain,
% 0.86/1.05      (((v2_struct_0 @ sk_A)
% 0.86/1.05        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.86/1.05  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('31', plain,
% 0.86/1.05      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('clc', [status(thm)], ['29', '30'])).
% 0.86/1.05  thf('32', plain,
% 0.86/1.05      (![X22 : $i, X23 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X22)
% 0.86/1.05          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.86/1.05      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.86/1.05  thf(d11_yellow_0, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( l1_orders_2 @ A ) =>
% 0.86/1.05       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.86/1.05  thf('33', plain,
% 0.86/1.05      (![X17 : $i]:
% 0.86/1.05         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 0.86/1.05          | ~ (l1_orders_2 @ X17))),
% 0.86/1.05      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.86/1.05  thf('34', plain,
% 0.86/1.05      (![X24 : $i]:
% 0.86/1.05         ((r1_yellow_0 @ X24 @ k1_xboole_0)
% 0.86/1.05          | ~ (l1_orders_2 @ X24)
% 0.86/1.05          | ~ (v1_yellow_0 @ X24)
% 0.86/1.05          | ~ (v5_orders_2 @ X24)
% 0.86/1.05          | (v2_struct_0 @ X24))),
% 0.86/1.05      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.86/1.05  thf('35', plain,
% 0.86/1.05      (![X22 : $i, X23 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X22)
% 0.86/1.05          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.86/1.05      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.86/1.05  thf('36', plain,
% 0.86/1.05      (![X25 : $i, X26 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.86/1.05          | (r2_lattice3 @ X26 @ k1_xboole_0 @ X25)
% 0.86/1.05          | ~ (l1_orders_2 @ X26))),
% 0.86/1.05      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.86/1.05  thf('37', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['35', '36'])).
% 0.86/1.05  thf('38', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | ~ (l1_orders_2 @ X0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['37'])).
% 0.86/1.05  thf('39', plain,
% 0.86/1.05      (![X22 : $i, X23 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X22)
% 0.86/1.05          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.86/1.05      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.86/1.05  thf('40', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.05         (~ (r1_yellow_0 @ X0 @ X1)
% 0.86/1.05          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.86/1.05          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.86/1.05          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.86/1.05          | ~ (l1_orders_2 @ X0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['18'])).
% 0.86/1.05  thf('41', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.86/1.05             (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | ~ (r1_yellow_0 @ X0 @ X2))),
% 0.86/1.05      inference('sup-', [status(thm)], ['39', '40'])).
% 0.86/1.05  thf('42', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.05         (~ (r1_yellow_0 @ X0 @ X2)
% 0.86/1.05          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.86/1.05             (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | ~ (l1_orders_2 @ X0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['41'])).
% 0.86/1.05  thf('43', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X1)
% 0.86/1.05          | ~ (l1_orders_2 @ X1)
% 0.86/1.05          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.86/1.05             (k1_yellow_0 @ X1 @ X0))
% 0.86/1.05          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['38', '42'])).
% 0.86/1.05  thf('44', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 0.86/1.05          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.86/1.05             (k1_yellow_0 @ X1 @ X0))
% 0.86/1.05          | ~ (l1_orders_2 @ X1))),
% 0.86/1.05      inference('simplify', [status(thm)], ['43'])).
% 0.86/1.05  thf('45', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((v2_struct_0 @ X0)
% 0.86/1.05          | ~ (v5_orders_2 @ X0)
% 0.86/1.05          | ~ (v1_yellow_0 @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.86/1.05             (k1_yellow_0 @ X0 @ X1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['34', '44'])).
% 0.86/1.05  thf('46', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.86/1.05           (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | ~ (v1_yellow_0 @ X0)
% 0.86/1.05          | ~ (v5_orders_2 @ X0)
% 0.86/1.05          | (v2_struct_0 @ X0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['45'])).
% 0.86/1.05  thf('47', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | (v2_struct_0 @ X0)
% 0.86/1.05          | ~ (v5_orders_2 @ X0)
% 0.86/1.05          | ~ (v1_yellow_0 @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0))),
% 0.86/1.05      inference('sup+', [status(thm)], ['33', '46'])).
% 0.86/1.05  thf('48', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (v1_yellow_0 @ X0)
% 0.86/1.05          | ~ (v5_orders_2 @ X0)
% 0.86/1.05          | (v2_struct_0 @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 0.86/1.05      inference('simplify', [status(thm)], ['47'])).
% 0.86/1.05  thf('49', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.86/1.05      inference('demod', [status(thm)], ['4', '5'])).
% 0.86/1.05  thf(d20_waybel_0, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( l1_orders_2 @ A ) =>
% 0.86/1.05       ( ![B:$i]:
% 0.86/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.05           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.86/1.05             ( ![C:$i]:
% 0.86/1.05               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.86/1.05                 ( ![D:$i]:
% 0.86/1.05                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.86/1.05                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.86/1.05                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.86/1.05  thf('50', plain,
% 0.86/1.05      (![X27 : $i, X28 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.86/1.05          | (r2_hidden @ (sk_C @ X27 @ X28) @ X27)
% 0.86/1.05          | (v13_waybel_0 @ X27 @ X28)
% 0.86/1.05          | ~ (l1_orders_2 @ X28))),
% 0.86/1.05      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.86/1.05  thf('51', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X0)
% 0.86/1.05          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 0.86/1.05          | (r2_hidden @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['49', '50'])).
% 0.86/1.05  thf(d1_xboole_0, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.86/1.05  thf('52', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.86/1.05      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.86/1.05  thf('53', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['51', '52'])).
% 0.86/1.05  thf('54', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.86/1.05      inference('demod', [status(thm)], ['4', '5'])).
% 0.86/1.05  thf('55', plain,
% 0.86/1.05      (![X27 : $i, X28 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.86/1.05          | (m1_subset_1 @ (sk_D_2 @ X27 @ X28) @ (u1_struct_0 @ X28))
% 0.86/1.05          | (v13_waybel_0 @ X27 @ X28)
% 0.86/1.05          | ~ (l1_orders_2 @ X28))),
% 0.86/1.05      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.86/1.05  thf('56', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X0)
% 0.86/1.05          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 0.86/1.05          | (m1_subset_1 @ (sk_D_2 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.86/1.05             (u1_struct_0 @ X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['54', '55'])).
% 0.86/1.05  thf(t2_subset, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ A @ B ) =>
% 0.86/1.05       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.86/1.05  thf('57', plain,
% 0.86/1.05      (![X12 : $i, X13 : $i]:
% 0.86/1.05         ((r2_hidden @ X12 @ X13)
% 0.86/1.05          | (v1_xboole_0 @ X13)
% 0.86/1.05          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.86/1.05      inference('cnf', [status(esa)], [t2_subset])).
% 0.86/1.05  thf('58', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.86/1.05          | (r2_hidden @ (sk_D_2 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.86/1.05             (u1_struct_0 @ X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['56', '57'])).
% 0.86/1.05  thf('59', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.86/1.05      inference('demod', [status(thm)], ['4', '5'])).
% 0.86/1.05  thf('60', plain,
% 0.86/1.05      (![X27 : $i, X28 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.86/1.05          | ~ (r2_hidden @ (sk_D_2 @ X27 @ X28) @ X27)
% 0.86/1.05          | (v13_waybel_0 @ X27 @ X28)
% 0.86/1.05          | ~ (l1_orders_2 @ X28))),
% 0.86/1.05      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.86/1.05  thf('61', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X0)
% 0.86/1.05          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 0.86/1.05          | ~ (r2_hidden @ (sk_D_2 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.86/1.05               (u1_struct_0 @ X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['59', '60'])).
% 0.86/1.05  thf('62', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 0.86/1.05          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['58', '61'])).
% 0.86/1.05  thf('63', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 0.86/1.05          | ~ (l1_orders_2 @ X0)
% 0.86/1.05          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.86/1.05      inference('simplify', [status(thm)], ['62'])).
% 0.86/1.05  thf('64', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X0) | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 0.86/1.05      inference('clc', [status(thm)], ['53', '63'])).
% 0.86/1.05  thf('65', plain,
% 0.86/1.05      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('split', [status(esa)], ['0'])).
% 0.86/1.05  thf('66', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf(t4_subset, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.86/1.05       ( m1_subset_1 @ A @ C ) ))).
% 0.86/1.05  thf('67', plain,
% 0.86/1.05      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.86/1.05         (~ (r2_hidden @ X14 @ X15)
% 0.86/1.05          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.86/1.05          | (m1_subset_1 @ X14 @ X16))),
% 0.86/1.05      inference('cnf', [status(esa)], [t4_subset])).
% 0.86/1.05  thf('68', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.86/1.05      inference('sup-', [status(thm)], ['66', '67'])).
% 0.86/1.05  thf('69', plain,
% 0.86/1.05      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['65', '68'])).
% 0.86/1.05  thf('70', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.86/1.05      inference('demod', [status(thm)], ['4', '5'])).
% 0.86/1.05  thf('71', plain,
% 0.86/1.05      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.86/1.05          | ~ (v13_waybel_0 @ X27 @ X28)
% 0.86/1.05          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.86/1.05          | (r2_hidden @ X29 @ X27)
% 0.86/1.05          | ~ (r1_orders_2 @ X28 @ X30 @ X29)
% 0.86/1.05          | ~ (r2_hidden @ X30 @ X27)
% 0.86/1.05          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.86/1.05          | ~ (l1_orders_2 @ X28))),
% 0.86/1.05      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.86/1.05  thf('72', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X0)
% 0.86/1.05          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.86/1.05          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.86/1.05          | ~ (r1_orders_2 @ X0 @ X1 @ X2)
% 0.86/1.05          | (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 0.86/1.05          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.86/1.05          | ~ (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['70', '71'])).
% 0.86/1.05  thf('73', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.86/1.05           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.86/1.05           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | ~ (l1_orders_2 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['69', '72'])).
% 0.86/1.05  thf('74', plain,
% 0.86/1.05      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('split', [status(esa)], ['0'])).
% 0.86/1.05  thf('75', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf(l3_subset_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.86/1.05       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.86/1.05  thf('76', plain,
% 0.86/1.05      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.86/1.05         (~ (r2_hidden @ X5 @ X6)
% 0.86/1.05          | (r2_hidden @ X5 @ X7)
% 0.86/1.05          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.86/1.05      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.86/1.05  thf('77', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.86/1.05      inference('sup-', [status(thm)], ['75', '76'])).
% 0.86/1.05  thf('78', plain,
% 0.86/1.05      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['74', '77'])).
% 0.86/1.05  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('80', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.86/1.05           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['73', '78', '79'])).
% 0.86/1.05  thf('81', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (l1_orders_2 @ sk_A)
% 0.86/1.05           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.86/1.05           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['64', '80'])).
% 0.86/1.05  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('83', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.86/1.05           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['81', '82'])).
% 0.86/1.05  thf('84', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (l1_orders_2 @ sk_A)
% 0.86/1.05           | (v2_struct_0 @ sk_A)
% 0.86/1.05           | ~ (v5_orders_2 @ sk_A)
% 0.86/1.05           | ~ (v1_yellow_0 @ sk_A)
% 0.86/1.05           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['48', '83'])).
% 0.86/1.05  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('86', plain, ((v5_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('87', plain, ((v1_yellow_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('88', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          ((v2_struct_0 @ sk_A)
% 0.86/1.05           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.86/1.05  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('90', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['88', '89'])).
% 0.86/1.05  thf('91', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (l1_orders_2 @ sk_A)
% 0.86/1.05           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['32', '90'])).
% 0.86/1.05  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('93', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['91', '92'])).
% 0.86/1.05  thf('94', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.86/1.05      inference('demod', [status(thm)], ['4', '5'])).
% 0.86/1.05  thf('95', plain,
% 0.86/1.05      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.86/1.05         (~ (r2_hidden @ X14 @ X15)
% 0.86/1.05          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.86/1.05          | (m1_subset_1 @ X14 @ X16))),
% 0.86/1.05      inference('cnf', [status(esa)], [t4_subset])).
% 0.86/1.05  thf('96', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['94', '95'])).
% 0.86/1.05  thf('97', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['93', '96'])).
% 0.86/1.05  thf('98', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('99', plain,
% 0.86/1.05      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.86/1.05          | ~ (v13_waybel_0 @ X27 @ X28)
% 0.86/1.05          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.86/1.05          | (r2_hidden @ X29 @ X27)
% 0.86/1.05          | ~ (r1_orders_2 @ X28 @ X30 @ X29)
% 0.86/1.05          | ~ (r2_hidden @ X30 @ X27)
% 0.86/1.05          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.86/1.05          | ~ (l1_orders_2 @ X28))),
% 0.86/1.05      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.86/1.05  thf('100', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ sk_A)
% 0.86/1.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.86/1.05          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.86/1.05          | (r2_hidden @ X1 @ sk_B_1)
% 0.86/1.05          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.86/1.05          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['98', '99'])).
% 0.86/1.05  thf('101', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('102', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('103', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.86/1.05          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.86/1.05          | (r2_hidden @ X1 @ sk_B_1)
% 0.86/1.05          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.86/1.05  thf('104', plain,
% 0.86/1.05      ((![X0 : $i, X1 : $i]:
% 0.86/1.05          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | (r2_hidden @ X1 @ sk_B_1)
% 0.86/1.05           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.86/1.05           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['97', '103'])).
% 0.86/1.05  thf('105', plain,
% 0.86/1.05      (![X17 : $i]:
% 0.86/1.05         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 0.86/1.05          | ~ (l1_orders_2 @ X17))),
% 0.86/1.05      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.86/1.05  thf('106', plain,
% 0.86/1.05      (![X24 : $i]:
% 0.86/1.05         ((r1_yellow_0 @ X24 @ k1_xboole_0)
% 0.86/1.05          | ~ (l1_orders_2 @ X24)
% 0.86/1.05          | ~ (v1_yellow_0 @ X24)
% 0.86/1.05          | ~ (v5_orders_2 @ X24)
% 0.86/1.05          | (v2_struct_0 @ X24))),
% 0.86/1.05      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.86/1.05  thf('107', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['93', '96'])).
% 0.86/1.05  thf('108', plain,
% 0.86/1.05      (![X25 : $i, X26 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.86/1.05          | (r2_lattice3 @ X26 @ k1_xboole_0 @ X25)
% 0.86/1.05          | ~ (l1_orders_2 @ X26))),
% 0.86/1.05      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.86/1.05  thf('109', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (l1_orders_2 @ sk_A)
% 0.86/1.05           | (r2_lattice3 @ sk_A @ k1_xboole_0 @ (k1_yellow_0 @ sk_A @ X0))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['107', '108'])).
% 0.86/1.05  thf('110', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('111', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (r2_lattice3 @ sk_A @ k1_xboole_0 @ (k1_yellow_0 @ sk_A @ X0)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['109', '110'])).
% 0.86/1.05  thf('112', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.05         (~ (r1_yellow_0 @ X0 @ X2)
% 0.86/1.05          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.86/1.05             (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.86/1.05          | ~ (l1_orders_2 @ X0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['41'])).
% 0.86/1.05  thf('113', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (l1_orders_2 @ sk_A)
% 0.86/1.05           | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05              (k1_yellow_0 @ sk_A @ X0))
% 0.86/1.05           | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['111', '112'])).
% 0.86/1.05  thf('114', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('115', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05            (k1_yellow_0 @ sk_A @ X0))
% 0.86/1.05           | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['113', '114'])).
% 0.86/1.05  thf('116', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          ((v2_struct_0 @ sk_A)
% 0.86/1.05           | ~ (v5_orders_2 @ sk_A)
% 0.86/1.05           | ~ (v1_yellow_0 @ sk_A)
% 0.86/1.05           | ~ (l1_orders_2 @ sk_A)
% 0.86/1.05           | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05              (k1_yellow_0 @ sk_A @ X0))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['106', '115'])).
% 0.86/1.05  thf('117', plain, ((v5_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('118', plain, ((v1_yellow_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('119', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('120', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          ((v2_struct_0 @ sk_A)
% 0.86/1.05           | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05              (k1_yellow_0 @ sk_A @ X0))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.86/1.05  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('122', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.86/1.05           (k1_yellow_0 @ sk_A @ X0)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['120', '121'])).
% 0.86/1.05  thf('123', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.86/1.05            (k1_yellow_0 @ sk_A @ X0))
% 0.86/1.05           | ~ (l1_orders_2 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup+', [status(thm)], ['105', '122'])).
% 0.86/1.05  thf('124', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('125', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.86/1.05           (k1_yellow_0 @ sk_A @ X0)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['123', '124'])).
% 0.86/1.05  thf('126', plain,
% 0.86/1.05      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['65', '68'])).
% 0.86/1.05  thf('127', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.86/1.05          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.86/1.05          | (r2_hidden @ X1 @ sk_B_1)
% 0.86/1.05          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.86/1.05  thf('128', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | (r2_hidden @ X0 @ sk_B_1)
% 0.86/1.05           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.86/1.05           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['126', '127'])).
% 0.86/1.05  thf('129', plain,
% 0.86/1.05      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('split', [status(esa)], ['0'])).
% 0.86/1.05  thf('130', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | (r2_hidden @ X0 @ sk_B_1)
% 0.86/1.05           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['128', '129'])).
% 0.86/1.05  thf('131', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.86/1.05           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['125', '130'])).
% 0.86/1.05  thf('132', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['93', '96'])).
% 0.86/1.05  thf('133', plain,
% 0.86/1.05      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['131', '132'])).
% 0.86/1.05  thf('134', plain,
% 0.86/1.05      ((![X0 : $i, X1 : $i]:
% 0.86/1.05          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.86/1.05           | (r2_hidden @ X1 @ sk_B_1)
% 0.86/1.05           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['104', '133'])).
% 0.86/1.05  thf('135', plain,
% 0.86/1.05      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05         | (r2_hidden @ 
% 0.86/1.05            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05            sk_B_1)
% 0.86/1.05         | ~ (m1_subset_1 @ 
% 0.86/1.05              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05              (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['31', '134'])).
% 0.86/1.05  thf('136', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('137', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.86/1.05      inference('demod', [status(thm)], ['4', '5'])).
% 0.86/1.05  thf('138', plain,
% 0.86/1.05      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.86/1.05          | ((X10) = (X8))
% 0.86/1.05          | ~ (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.86/1.05          | ~ (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X8)
% 0.86/1.05          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.86/1.05  thf('139', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.86/1.05          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.86/1.05          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.86/1.05          | ((X1) = (X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['137', '138'])).
% 0.86/1.05  thf('140', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | ~ (r2_hidden @ 
% 0.86/1.05             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05             sk_B_1)
% 0.86/1.05        | ~ (r2_hidden @ 
% 0.86/1.05             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05             (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['136', '139'])).
% 0.86/1.05  thf('141', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.86/1.05      inference('sup-', [status(thm)], ['75', '76'])).
% 0.86/1.05  thf('142', plain,
% 0.86/1.05      ((~ (r2_hidden @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05           sk_B_1)
% 0.86/1.05        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('clc', [status(thm)], ['140', '141'])).
% 0.86/1.05  thf('143', plain,
% 0.86/1.05      (((~ (m1_subset_1 @ 
% 0.86/1.05            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05            (u1_struct_0 @ sk_A))
% 0.86/1.05         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['135', '142'])).
% 0.86/1.05  thf('144', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.86/1.05        | (m1_subset_1 @ 
% 0.86/1.05           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05           (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['3', '8'])).
% 0.86/1.05  thf('145', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['143', '144'])).
% 0.86/1.05  thf('146', plain,
% 0.86/1.05      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.86/1.05        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('147', plain,
% 0.86/1.05      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('split', [status(esa)], ['146'])).
% 0.86/1.05  thf('148', plain,
% 0.86/1.05      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.86/1.05         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.86/1.05             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('sup+', [status(thm)], ['145', '147'])).
% 0.86/1.05  thf(fc14_subset_1, axiom,
% 0.86/1.05    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.86/1.05  thf('149', plain, (![X11 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X11) @ X11)),
% 0.86/1.05      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.86/1.05  thf('150', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.86/1.05      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.86/1.05  thf('151', plain, (![X11 : $i]: ~ (v1_subset_1 @ X11 @ X11)),
% 0.86/1.05      inference('demod', [status(thm)], ['149', '150'])).
% 0.86/1.05  thf('152', plain,
% 0.86/1.05      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.86/1.05       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['148', '151'])).
% 0.86/1.05  thf('153', plain,
% 0.86/1.05      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.86/1.05       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('split', [status(esa)], ['146'])).
% 0.86/1.05  thf('154', plain,
% 0.86/1.05      (![X17 : $i]:
% 0.86/1.05         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 0.86/1.05          | ~ (l1_orders_2 @ X17))),
% 0.86/1.05      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.86/1.05  thf('155', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf(d7_subset_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.86/1.05       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.86/1.05  thf('156', plain,
% 0.86/1.05      (![X31 : $i, X32 : $i]:
% 0.86/1.05         (((X32) = (X31))
% 0.86/1.05          | (v1_subset_1 @ X32 @ X31)
% 0.86/1.05          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.86/1.05      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.86/1.05  thf('157', plain,
% 0.86/1.05      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.86/1.05        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['155', '156'])).
% 0.86/1.05  thf('158', plain,
% 0.86/1.05      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('split', [status(esa)], ['0'])).
% 0.86/1.05  thf('159', plain,
% 0.86/1.05      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['157', '158'])).
% 0.86/1.05  thf('160', plain,
% 0.86/1.05      (![X22 : $i, X23 : $i]:
% 0.86/1.05         (~ (l1_orders_2 @ X22)
% 0.86/1.05          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.86/1.05      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.86/1.05  thf('161', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.86/1.05           | ~ (l1_orders_2 @ sk_A)))
% 0.86/1.05         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('sup+', [status(thm)], ['159', '160'])).
% 0.86/1.05  thf('162', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('163', plain,
% 0.86/1.05      ((![X0 : $i]: (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.86/1.05         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('demod', [status(thm)], ['161', '162'])).
% 0.86/1.05  thf('164', plain,
% 0.86/1.05      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1) | ~ (l1_orders_2 @ sk_A)))
% 0.86/1.05         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('sup+', [status(thm)], ['154', '163'])).
% 0.86/1.05  thf('165', plain, ((l1_orders_2 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('166', plain,
% 0.86/1.05      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.86/1.05         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('demod', [status(thm)], ['164', '165'])).
% 0.86/1.05  thf('167', plain,
% 0.86/1.05      (![X12 : $i, X13 : $i]:
% 0.86/1.05         ((r2_hidden @ X12 @ X13)
% 0.86/1.05          | (v1_xboole_0 @ X13)
% 0.86/1.05          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.86/1.05      inference('cnf', [status(esa)], [t2_subset])).
% 0.86/1.05  thf('168', plain,
% 0.86/1.05      ((((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.86/1.05         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['166', '167'])).
% 0.86/1.05  thf('169', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('170', plain,
% 0.86/1.05      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.86/1.05         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('clc', [status(thm)], ['168', '169'])).
% 0.86/1.05  thf('171', plain,
% 0.86/1.05      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.86/1.05         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.86/1.05      inference('split', [status(esa)], ['146'])).
% 0.86/1.05  thf('172', plain,
% 0.86/1.05      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.86/1.05       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['170', '171'])).
% 0.86/1.05  thf('173', plain, ($false),
% 0.86/1.05      inference('sat_resolution*', [status(thm)], ['1', '152', '153', '172'])).
% 0.86/1.05  
% 0.86/1.05  % SZS output end Refutation
% 0.86/1.05  
% 0.86/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
