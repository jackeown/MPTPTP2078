%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wB4nZQvI2t

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:11 EST 2020

% Result     : Theorem 10.31s
% Output     : Refutation 10.31s
% Verified   : 
% Statistics : Number of formulae       :  258 (1038 expanded)
%              Number of leaves         :   43 ( 328 expanded)
%              Depth                    :   39
%              Number of atoms          : 2747 (13786 expanded)
%              Number of equality atoms :   42 ( 189 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X26: $i] :
      ( ( r1_yellow_0 @ X26 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v1_yellow_0 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('5',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 = X31 )
      | ( v1_subset_1 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B_1 @ X0 ) @ X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

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

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( X8 = X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_2 )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

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

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X17 @ X16 ) @ X17 )
      | ( r2_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k1_yellow_0 @ X20 @ X21 ) )
      | ~ ( r2_lattice3 @ X20 @ X21 @ X23 )
      | ( r1_orders_2 @ X20 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_yellow_0 @ X20 @ X21 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( r1_yellow_0 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r1_orders_2 @ X20 @ ( k1_yellow_0 @ X20 @ X21 ) @ X23 )
      | ~ ( r2_lattice3 @ X20 @ X21 @ X23 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_2
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('48',plain,(
    ! [X26: $i] :
      ( ( r1_yellow_0 @ X26 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v1_yellow_0 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X17 @ X16 ) @ X17 )
      | ( r2_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k1_yellow_0 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ X2 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

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

thf('66',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ ( sk_C @ X27 @ X28 ) @ X27 )
      | ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('71',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D_3 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('73',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_3 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('76',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ ( sk_D_3 @ X27 @ X28 ) @ X27 )
      | ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_3 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['69','79'])).

thf('81',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('82',plain,(
    ! [X19: $i] :
      ( ( ( k3_yellow_0 @ X19 )
        = ( k1_yellow_0 @ X19 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('83',plain,(
    ! [X26: $i] :
      ( ( r1_yellow_0 @ X26 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v1_yellow_0 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('84',plain,(
    ! [X19: $i] :
      ( ( ( k3_yellow_0 @ X19 )
        = ( k1_yellow_0 @ X19 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('85',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X17 @ X16 ) @ X17 )
      | ( r2_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k3_yellow_0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X19: $i] :
      ( ( ( k3_yellow_0 @ X19 )
        = ( k1_yellow_0 @ X19 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['69','79'])).

thf('106',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('108',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('110',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('112',plain,(
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

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('116',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['105','117'])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['104','120'])).

thf('122',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['81','127'])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k1_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['130','134'])).

thf('136',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['80','137'])).

thf('139',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['64','140'])).

thf('142',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['47','147'])).

thf('149',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('152',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
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

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v13_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_2 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    ! [X19: $i] :
      ( ( ( k3_yellow_0 @ X19 )
        = ( k1_yellow_0 @ X19 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('166',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_2 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('168',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_2 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['163','168'])).

thf('170',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('174',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_2 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['159','176'])).

thf('178',plain,
    ( ( ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_2 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['46','177'])).

thf('179',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('181',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( X8 = X6 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_2 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('185',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_2
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['178','185'])).

thf('187',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('188',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['189'])).

thf('191',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['188','190'])).

thf('192',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('194',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ X9 @ X9 ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['191','194'])).

thf('196',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['189'])).

thf('197',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 = X31 )
      | ( v1_subset_1 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('199',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('201',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('203',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['201','204'])).

thf('206',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('207',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('211',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['189'])).

thf('212',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','195','196','212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wB4nZQvI2t
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 10.31/10.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.31/10.52  % Solved by: fo/fo7.sh
% 10.31/10.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.31/10.52  % done 4359 iterations in 10.051s
% 10.31/10.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.31/10.52  % SZS output start Refutation
% 10.31/10.52  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 10.31/10.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 10.31/10.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 10.31/10.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 10.31/10.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 10.31/10.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.31/10.52  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 10.31/10.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 10.31/10.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.31/10.52  thf(sk_A_type, type, sk_A: $i).
% 10.31/10.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.31/10.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.31/10.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 10.31/10.52  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 10.31/10.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.31/10.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 10.31/10.52  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 10.31/10.52  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 10.31/10.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.31/10.52  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 10.31/10.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 10.31/10.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.31/10.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 10.31/10.52  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 10.31/10.52  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 10.31/10.52  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 10.31/10.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 10.31/10.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 10.31/10.52  thf(t8_waybel_7, conjecture,
% 10.31/10.52    (![A:$i]:
% 10.31/10.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 10.31/10.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 10.31/10.52         ( l1_orders_2 @ A ) ) =>
% 10.31/10.52       ( ![B:$i]:
% 10.31/10.52         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 10.31/10.52             ( v13_waybel_0 @ B @ A ) & 
% 10.31/10.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.31/10.52           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 10.31/10.52             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 10.31/10.52  thf(zf_stmt_0, negated_conjecture,
% 10.31/10.52    (~( ![A:$i]:
% 10.31/10.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 10.31/10.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 10.31/10.52            ( l1_orders_2 @ A ) ) =>
% 10.31/10.52          ( ![B:$i]:
% 10.31/10.52            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 10.31/10.52                ( v13_waybel_0 @ B @ A ) & 
% 10.31/10.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.31/10.52              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 10.31/10.52                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 10.31/10.52    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 10.31/10.52  thf('0', plain,
% 10.31/10.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)
% 10.31/10.52        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('1', plain,
% 10.31/10.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)) | 
% 10.31/10.52       ~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('split', [status(esa)], ['0'])).
% 10.31/10.52  thf(t42_yellow_0, axiom,
% 10.31/10.52    (![A:$i]:
% 10.31/10.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 10.31/10.52         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 10.31/10.52       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 10.31/10.52         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 10.31/10.52  thf('2', plain,
% 10.31/10.52      (![X26 : $i]:
% 10.31/10.52         ((r1_yellow_0 @ X26 @ k1_xboole_0)
% 10.31/10.52          | ~ (l1_orders_2 @ X26)
% 10.31/10.52          | ~ (v1_yellow_0 @ X26)
% 10.31/10.52          | ~ (v5_orders_2 @ X26)
% 10.31/10.52          | (v2_struct_0 @ X26))),
% 10.31/10.52      inference('cnf', [status(esa)], [t42_yellow_0])).
% 10.31/10.52  thf('3', plain,
% 10.31/10.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf(rc3_subset_1, axiom,
% 10.31/10.52    (![A:$i]:
% 10.31/10.52     ( ?[B:$i]:
% 10.31/10.52       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 10.31/10.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 10.31/10.52  thf('4', plain,
% 10.31/10.52      (![X9 : $i]: (m1_subset_1 @ (sk_B_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 10.31/10.52  thf('5', plain,
% 10.31/10.52      (![X9 : $i]: (m1_subset_1 @ (sk_B_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 10.31/10.52  thf(d7_subset_1, axiom,
% 10.31/10.52    (![A:$i,B:$i]:
% 10.31/10.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.31/10.52       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 10.31/10.52  thf('6', plain,
% 10.31/10.52      (![X31 : $i, X32 : $i]:
% 10.31/10.52         (((X32) = (X31))
% 10.31/10.52          | (v1_subset_1 @ X32 @ X31)
% 10.31/10.52          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 10.31/10.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 10.31/10.52  thf('7', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((v1_subset_1 @ (sk_B_1 @ X0) @ X0) | ((sk_B_1 @ X0) = (X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['5', '6'])).
% 10.31/10.52  thf('8', plain, (![X9 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X9) @ X9)),
% 10.31/10.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 10.31/10.52  thf('9', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (X0))),
% 10.31/10.52      inference('clc', [status(thm)], ['7', '8'])).
% 10.31/10.52  thf('10', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('demod', [status(thm)], ['4', '9'])).
% 10.31/10.52  thf(t8_subset_1, axiom,
% 10.31/10.52    (![A:$i,B:$i]:
% 10.31/10.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.31/10.52       ( ![C:$i]:
% 10.31/10.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.31/10.52           ( ( ![D:$i]:
% 10.31/10.52               ( ( m1_subset_1 @ D @ A ) =>
% 10.31/10.52                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 10.31/10.52             ( ( B ) = ( C ) ) ) ) ) ))).
% 10.31/10.52  thf('11', plain,
% 10.31/10.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 10.31/10.52          | ((X8) = (X6))
% 10.31/10.52          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 10.31/10.52          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 10.31/10.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 10.31/10.52      inference('cnf', [status(esa)], [t8_subset_1])).
% 10.31/10.52  thf('12', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 10.31/10.52          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 10.31/10.52          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 10.31/10.52          | ((X1) = (X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['10', '11'])).
% 10.31/10.52  thf('13', plain,
% 10.31/10.52      ((((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52        | (r2_hidden @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52           sk_B_2)
% 10.31/10.52        | (r2_hidden @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52           (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['3', '12'])).
% 10.31/10.52  thf('14', plain,
% 10.31/10.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf(l3_subset_1, axiom,
% 10.31/10.52    (![A:$i,B:$i]:
% 10.31/10.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.31/10.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 10.31/10.52  thf('15', plain,
% 10.31/10.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 10.31/10.52         (~ (r2_hidden @ X3 @ X4)
% 10.31/10.52          | (r2_hidden @ X3 @ X5)
% 10.31/10.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 10.31/10.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 10.31/10.52  thf('16', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 10.31/10.52      inference('sup-', [status(thm)], ['14', '15'])).
% 10.31/10.52  thf('17', plain,
% 10.31/10.52      (((r2_hidden @ 
% 10.31/10.52         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52         (u1_struct_0 @ sk_A))
% 10.31/10.52        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('clc', [status(thm)], ['13', '16'])).
% 10.31/10.52  thf('18', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('demod', [status(thm)], ['4', '9'])).
% 10.31/10.52  thf(t4_subset, axiom,
% 10.31/10.52    (![A:$i,B:$i,C:$i]:
% 10.31/10.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 10.31/10.52       ( m1_subset_1 @ A @ C ) ))).
% 10.31/10.52  thf('19', plain,
% 10.31/10.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.31/10.52         (~ (r2_hidden @ X12 @ X13)
% 10.31/10.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 10.31/10.52          | (m1_subset_1 @ X12 @ X14))),
% 10.31/10.52      inference('cnf', [status(esa)], [t4_subset])).
% 10.31/10.52  thf('20', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['18', '19'])).
% 10.31/10.52  thf('21', plain,
% 10.31/10.52      ((((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52        | (m1_subset_1 @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52           (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['17', '20'])).
% 10.31/10.52  thf(d9_lattice3, axiom,
% 10.31/10.52    (![A:$i]:
% 10.31/10.52     ( ( l1_orders_2 @ A ) =>
% 10.31/10.52       ( ![B:$i,C:$i]:
% 10.31/10.52         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.31/10.52           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 10.31/10.52             ( ![D:$i]:
% 10.31/10.52               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 10.31/10.52                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 10.31/10.52  thf('22', plain,
% 10.31/10.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 10.31/10.52          | (r2_hidden @ (sk_D_1 @ X15 @ X17 @ X16) @ X17)
% 10.31/10.52          | (r2_lattice3 @ X16 @ X17 @ X15)
% 10.31/10.52          | ~ (l1_orders_2 @ X16))),
% 10.31/10.52      inference('cnf', [status(esa)], [d9_lattice3])).
% 10.31/10.52  thf('23', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (l1_orders_2 @ sk_A)
% 10.31/10.52          | (r2_lattice3 @ sk_A @ X0 @ 
% 10.31/10.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | (r2_hidden @ 
% 10.31/10.52             (sk_D_1 @ 
% 10.31/10.52              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52              X0 @ sk_A) @ 
% 10.31/10.52             X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['21', '22'])).
% 10.31/10.52  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('25', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52          | (r2_lattice3 @ sk_A @ X0 @ 
% 10.31/10.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | (r2_hidden @ 
% 10.31/10.52             (sk_D_1 @ 
% 10.31/10.52              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52              X0 @ sk_A) @ 
% 10.31/10.52             X0))),
% 10.31/10.52      inference('demod', [status(thm)], ['23', '24'])).
% 10.31/10.52  thf(d1_xboole_0, axiom,
% 10.31/10.52    (![A:$i]:
% 10.31/10.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 10.31/10.52  thf('26', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 10.31/10.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.31/10.52  thf('27', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((r2_lattice3 @ sk_A @ X0 @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | ((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (v1_xboole_0 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['25', '26'])).
% 10.31/10.52  thf('28', plain,
% 10.31/10.52      ((((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52        | (m1_subset_1 @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52           (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['17', '20'])).
% 10.31/10.52  thf(dt_k1_yellow_0, axiom,
% 10.31/10.52    (![A:$i,B:$i]:
% 10.31/10.52     ( ( l1_orders_2 @ A ) =>
% 10.31/10.52       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 10.31/10.52  thf('29', plain,
% 10.31/10.52      (![X24 : $i, X25 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X24)
% 10.31/10.52          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 10.31/10.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 10.31/10.52  thf(d9_yellow_0, axiom,
% 10.31/10.52    (![A:$i]:
% 10.31/10.52     ( ( l1_orders_2 @ A ) =>
% 10.31/10.52       ( ![B:$i,C:$i]:
% 10.31/10.52         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.31/10.52           ( ( r1_yellow_0 @ A @ B ) =>
% 10.31/10.52             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 10.31/10.52               ( ( r2_lattice3 @ A @ B @ C ) & 
% 10.31/10.52                 ( ![D:$i]:
% 10.31/10.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 10.31/10.52                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 10.31/10.52                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 10.31/10.52  thf('30', plain,
% 10.31/10.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 10.31/10.52         (((X22) != (k1_yellow_0 @ X20 @ X21))
% 10.31/10.52          | ~ (r2_lattice3 @ X20 @ X21 @ X23)
% 10.31/10.52          | (r1_orders_2 @ X20 @ X22 @ X23)
% 10.31/10.52          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 10.31/10.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 10.31/10.52          | ~ (r1_yellow_0 @ X20 @ X21)
% 10.31/10.52          | ~ (l1_orders_2 @ X20))),
% 10.31/10.52      inference('cnf', [status(esa)], [d9_yellow_0])).
% 10.31/10.52  thf('31', plain,
% 10.31/10.52      (![X20 : $i, X21 : $i, X23 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X20)
% 10.31/10.52          | ~ (r1_yellow_0 @ X20 @ X21)
% 10.31/10.52          | ~ (m1_subset_1 @ (k1_yellow_0 @ X20 @ X21) @ (u1_struct_0 @ X20))
% 10.31/10.52          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 10.31/10.52          | (r1_orders_2 @ X20 @ (k1_yellow_0 @ X20 @ X21) @ X23)
% 10.31/10.52          | ~ (r2_lattice3 @ X20 @ X21 @ X23))),
% 10.31/10.52      inference('simplify', [status(thm)], ['30'])).
% 10.31/10.52  thf('32', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 10.31/10.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (r1_yellow_0 @ X0 @ X1)
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['29', '31'])).
% 10.31/10.52  thf('33', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (r1_yellow_0 @ X0 @ X1)
% 10.31/10.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 10.31/10.52          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['32'])).
% 10.31/10.52  thf('34', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (l1_orders_2 @ sk_A)
% 10.31/10.52          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 10.31/10.52               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 10.31/10.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['28', '33'])).
% 10.31/10.52  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('36', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 10.31/10.52               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 10.31/10.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 10.31/10.52      inference('demod', [status(thm)], ['34', '35'])).
% 10.31/10.52  thf('37', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (v1_xboole_0 @ X0)
% 10.31/10.52          | ((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (r1_yellow_0 @ sk_A @ X0)
% 10.31/10.52          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 10.31/10.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['27', '36'])).
% 10.31/10.52  thf('38', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52          | ~ (r1_yellow_0 @ sk_A @ X0)
% 10.31/10.52          | ((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (v1_xboole_0 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['37'])).
% 10.31/10.52  thf('39', plain,
% 10.31/10.52      (((v2_struct_0 @ sk_A)
% 10.31/10.52        | ~ (v5_orders_2 @ sk_A)
% 10.31/10.52        | ~ (v1_yellow_0 @ sk_A)
% 10.31/10.52        | ~ (l1_orders_2 @ sk_A)
% 10.31/10.52        | ~ (v1_xboole_0 @ k1_xboole_0)
% 10.31/10.52        | ((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('sup-', [status(thm)], ['2', '38'])).
% 10.31/10.52  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('41', plain, ((v1_yellow_0 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 10.31/10.52  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.31/10.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.31/10.52  thf('44', plain,
% 10.31/10.52      (((v2_struct_0 @ sk_A)
% 10.31/10.52        | ((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 10.31/10.52  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('46', plain,
% 10.31/10.52      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('clc', [status(thm)], ['44', '45'])).
% 10.31/10.52  thf('47', plain,
% 10.31/10.52      (![X24 : $i, X25 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X24)
% 10.31/10.52          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 10.31/10.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 10.31/10.52  thf('48', plain,
% 10.31/10.52      (![X26 : $i]:
% 10.31/10.52         ((r1_yellow_0 @ X26 @ k1_xboole_0)
% 10.31/10.52          | ~ (l1_orders_2 @ X26)
% 10.31/10.52          | ~ (v1_yellow_0 @ X26)
% 10.31/10.52          | ~ (v5_orders_2 @ X26)
% 10.31/10.52          | (v2_struct_0 @ X26))),
% 10.31/10.52      inference('cnf', [status(esa)], [t42_yellow_0])).
% 10.31/10.52  thf('49', plain,
% 10.31/10.52      (![X24 : $i, X25 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X24)
% 10.31/10.52          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 10.31/10.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 10.31/10.52  thf('50', plain,
% 10.31/10.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 10.31/10.52          | (r2_hidden @ (sk_D_1 @ X15 @ X17 @ X16) @ X17)
% 10.31/10.52          | (r2_lattice3 @ X16 @ X17 @ X15)
% 10.31/10.52          | ~ (l1_orders_2 @ X16))),
% 10.31/10.52      inference('cnf', [status(esa)], [d9_lattice3])).
% 10.31/10.52  thf('51', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | (r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2))),
% 10.31/10.52      inference('sup-', [status(thm)], ['49', '50'])).
% 10.31/10.52  thf('52', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         ((r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2)
% 10.31/10.52          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['51'])).
% 10.31/10.52  thf('53', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 10.31/10.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.31/10.52  thf('54', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X1)
% 10.31/10.52          | (r2_lattice3 @ X1 @ X0 @ (k1_yellow_0 @ X1 @ X2))
% 10.31/10.52          | ~ (v1_xboole_0 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['52', '53'])).
% 10.31/10.52  thf('55', plain,
% 10.31/10.52      (![X24 : $i, X25 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X24)
% 10.31/10.52          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 10.31/10.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 10.31/10.52  thf('56', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (r1_yellow_0 @ X0 @ X1)
% 10.31/10.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 10.31/10.52          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['32'])).
% 10.31/10.52  thf('57', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (r1_yellow_0 @ X0 @ X2))),
% 10.31/10.52      inference('sup-', [status(thm)], ['55', '56'])).
% 10.31/10.52  thf('58', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (r1_yellow_0 @ X0 @ X2)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['57'])).
% 10.31/10.52  thf('59', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (v1_xboole_0 @ X2)
% 10.31/10.52          | ~ (l1_orders_2 @ X1)
% 10.31/10.52          | ~ (l1_orders_2 @ X1)
% 10.31/10.52          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 10.31/10.52             (k1_yellow_0 @ X1 @ X0))
% 10.31/10.52          | ~ (r1_yellow_0 @ X1 @ X2))),
% 10.31/10.52      inference('sup-', [status(thm)], ['54', '58'])).
% 10.31/10.52  thf('60', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (r1_yellow_0 @ X1 @ X2)
% 10.31/10.52          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 10.31/10.52             (k1_yellow_0 @ X1 @ X0))
% 10.31/10.52          | ~ (l1_orders_2 @ X1)
% 10.31/10.52          | ~ (v1_xboole_0 @ X2))),
% 10.31/10.52      inference('simplify', [status(thm)], ['59'])).
% 10.31/10.52  thf('61', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         ((v2_struct_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_xboole_0 @ k1_xboole_0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ X1)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['48', '60'])).
% 10.31/10.52  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.31/10.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.31/10.52  thf('63', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         ((v2_struct_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ X1)))),
% 10.31/10.52      inference('demod', [status(thm)], ['61', '62'])).
% 10.31/10.52  thf('64', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 10.31/10.52           (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | (v2_struct_0 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['63'])).
% 10.31/10.52  thf('65', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('demod', [status(thm)], ['4', '9'])).
% 10.31/10.52  thf(d20_waybel_0, axiom,
% 10.31/10.52    (![A:$i]:
% 10.31/10.52     ( ( l1_orders_2 @ A ) =>
% 10.31/10.52       ( ![B:$i]:
% 10.31/10.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.31/10.52           ( ( v13_waybel_0 @ B @ A ) <=>
% 10.31/10.52             ( ![C:$i]:
% 10.31/10.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.31/10.52                 ( ![D:$i]:
% 10.31/10.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 10.31/10.52                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 10.31/10.52                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 10.31/10.52  thf('66', plain,
% 10.31/10.52      (![X27 : $i, X28 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 10.31/10.52          | (r2_hidden @ (sk_C @ X27 @ X28) @ X27)
% 10.31/10.52          | (v13_waybel_0 @ X27 @ X28)
% 10.31/10.52          | ~ (l1_orders_2 @ X28))),
% 10.31/10.52      inference('cnf', [status(esa)], [d20_waybel_0])).
% 10.31/10.52  thf('67', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | (r2_hidden @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['65', '66'])).
% 10.31/10.52  thf('68', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 10.31/10.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.31/10.52  thf('69', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['67', '68'])).
% 10.31/10.52  thf('70', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('demod', [status(thm)], ['4', '9'])).
% 10.31/10.52  thf('71', plain,
% 10.31/10.52      (![X27 : $i, X28 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 10.31/10.52          | (m1_subset_1 @ (sk_D_3 @ X27 @ X28) @ (u1_struct_0 @ X28))
% 10.31/10.52          | (v13_waybel_0 @ X27 @ X28)
% 10.31/10.52          | ~ (l1_orders_2 @ X28))),
% 10.31/10.52      inference('cnf', [status(esa)], [d20_waybel_0])).
% 10.31/10.52  thf('72', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | (m1_subset_1 @ (sk_D_3 @ (u1_struct_0 @ X0) @ X0) @ 
% 10.31/10.52             (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['70', '71'])).
% 10.31/10.52  thf(t2_subset, axiom,
% 10.31/10.52    (![A:$i,B:$i]:
% 10.31/10.52     ( ( m1_subset_1 @ A @ B ) =>
% 10.31/10.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 10.31/10.52  thf('73', plain,
% 10.31/10.52      (![X10 : $i, X11 : $i]:
% 10.31/10.52         ((r2_hidden @ X10 @ X11)
% 10.31/10.52          | (v1_xboole_0 @ X11)
% 10.31/10.52          | ~ (m1_subset_1 @ X10 @ X11))),
% 10.31/10.52      inference('cnf', [status(esa)], [t2_subset])).
% 10.31/10.52  thf('74', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 10.31/10.52          | (r2_hidden @ (sk_D_3 @ (u1_struct_0 @ X0) @ X0) @ 
% 10.31/10.52             (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['72', '73'])).
% 10.31/10.52  thf('75', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('demod', [status(thm)], ['4', '9'])).
% 10.31/10.52  thf('76', plain,
% 10.31/10.52      (![X27 : $i, X28 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 10.31/10.52          | ~ (r2_hidden @ (sk_D_3 @ X27 @ X28) @ X27)
% 10.31/10.52          | (v13_waybel_0 @ X27 @ X28)
% 10.31/10.52          | ~ (l1_orders_2 @ X28))),
% 10.31/10.52      inference('cnf', [status(esa)], [d20_waybel_0])).
% 10.31/10.52  thf('77', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | ~ (r2_hidden @ (sk_D_3 @ (u1_struct_0 @ X0) @ X0) @ 
% 10.31/10.52               (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['75', '76'])).
% 10.31/10.52  thf('78', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['74', '77'])).
% 10.31/10.52  thf('79', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('simplify', [status(thm)], ['78'])).
% 10.31/10.52  thf('80', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0) | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 10.31/10.52      inference('clc', [status(thm)], ['69', '79'])).
% 10.31/10.52  thf('81', plain,
% 10.31/10.52      (![X24 : $i, X25 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X24)
% 10.31/10.52          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 10.31/10.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 10.31/10.52  thf(d11_yellow_0, axiom,
% 10.31/10.52    (![A:$i]:
% 10.31/10.52     ( ( l1_orders_2 @ A ) =>
% 10.31/10.52       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 10.31/10.52  thf('82', plain,
% 10.31/10.52      (![X19 : $i]:
% 10.31/10.52         (((k3_yellow_0 @ X19) = (k1_yellow_0 @ X19 @ k1_xboole_0))
% 10.31/10.52          | ~ (l1_orders_2 @ X19))),
% 10.31/10.52      inference('cnf', [status(esa)], [d11_yellow_0])).
% 10.31/10.52  thf('83', plain,
% 10.31/10.52      (![X26 : $i]:
% 10.31/10.52         ((r1_yellow_0 @ X26 @ k1_xboole_0)
% 10.31/10.52          | ~ (l1_orders_2 @ X26)
% 10.31/10.52          | ~ (v1_yellow_0 @ X26)
% 10.31/10.52          | ~ (v5_orders_2 @ X26)
% 10.31/10.52          | (v2_struct_0 @ X26))),
% 10.31/10.52      inference('cnf', [status(esa)], [t42_yellow_0])).
% 10.31/10.52  thf('84', plain,
% 10.31/10.52      (![X19 : $i]:
% 10.31/10.52         (((k3_yellow_0 @ X19) = (k1_yellow_0 @ X19 @ k1_xboole_0))
% 10.31/10.52          | ~ (l1_orders_2 @ X19))),
% 10.31/10.52      inference('cnf', [status(esa)], [d11_yellow_0])).
% 10.31/10.52  thf('85', plain,
% 10.31/10.52      (![X24 : $i, X25 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X24)
% 10.31/10.52          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 10.31/10.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 10.31/10.52  thf('86', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('sup+', [status(thm)], ['84', '85'])).
% 10.31/10.52  thf('87', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('simplify', [status(thm)], ['86'])).
% 10.31/10.52  thf('88', plain,
% 10.31/10.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 10.31/10.52          | (r2_hidden @ (sk_D_1 @ X15 @ X17 @ X16) @ X17)
% 10.31/10.52          | (r2_lattice3 @ X16 @ X17 @ X15)
% 10.31/10.52          | ~ (l1_orders_2 @ X16))),
% 10.31/10.52      inference('cnf', [status(esa)], [d9_lattice3])).
% 10.31/10.52  thf('89', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 10.31/10.52          | (r2_hidden @ (sk_D_1 @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1))),
% 10.31/10.52      inference('sup-', [status(thm)], ['87', '88'])).
% 10.31/10.52  thf('90', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         ((r2_hidden @ (sk_D_1 @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1)
% 10.31/10.52          | (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['89'])).
% 10.31/10.52  thf('91', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 10.31/10.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.31/10.52  thf('92', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X1)
% 10.31/10.52          | (r2_lattice3 @ X1 @ X0 @ (k3_yellow_0 @ X1))
% 10.31/10.52          | ~ (v1_xboole_0 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['90', '91'])).
% 10.31/10.52  thf('93', plain,
% 10.31/10.52      (![X19 : $i]:
% 10.31/10.52         (((k3_yellow_0 @ X19) = (k1_yellow_0 @ X19 @ k1_xboole_0))
% 10.31/10.52          | ~ (l1_orders_2 @ X19))),
% 10.31/10.52      inference('cnf', [status(esa)], [d11_yellow_0])).
% 10.31/10.52  thf('94', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (r1_yellow_0 @ X0 @ X2)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['57'])).
% 10.31/10.52  thf('95', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 10.31/10.52          | ~ (r1_yellow_0 @ X0 @ X1))),
% 10.31/10.52      inference('sup-', [status(thm)], ['93', '94'])).
% 10.31/10.52  thf('96', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (r1_yellow_0 @ X0 @ X1)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0)))),
% 10.31/10.52      inference('simplify', [status(thm)], ['95'])).
% 10.31/10.52  thf('97', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (v1_xboole_0 @ X1)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 10.31/10.52          | ~ (r1_yellow_0 @ X0 @ X1))),
% 10.31/10.52      inference('sup-', [status(thm)], ['92', '96'])).
% 10.31/10.52  thf('98', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (r1_yellow_0 @ X0 @ X1)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_xboole_0 @ X1))),
% 10.31/10.52      inference('simplify', [status(thm)], ['97'])).
% 10.31/10.52  thf('99', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((v2_struct_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_xboole_0 @ k1_xboole_0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['83', '98'])).
% 10.31/10.52  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.31/10.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.31/10.52  thf('101', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((v2_struct_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 10.31/10.52      inference('demod', [status(thm)], ['99', '100'])).
% 10.31/10.52  thf('102', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 10.31/10.52           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | (v2_struct_0 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['101'])).
% 10.31/10.52  thf('103', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 10.31/10.52           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v2_struct_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('sup+', [status(thm)], ['82', '102'])).
% 10.31/10.52  thf('104', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | (v2_struct_0 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 10.31/10.52             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 10.31/10.52      inference('simplify', [status(thm)], ['103'])).
% 10.31/10.52  thf('105', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0) | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 10.31/10.52      inference('clc', [status(thm)], ['69', '79'])).
% 10.31/10.52  thf('106', plain,
% 10.31/10.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('split', [status(esa)], ['0'])).
% 10.31/10.52  thf('107', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 10.31/10.52      inference('sup-', [status(thm)], ['14', '15'])).
% 10.31/10.52  thf('108', plain,
% 10.31/10.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['106', '107'])).
% 10.31/10.52  thf('109', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['18', '19'])).
% 10.31/10.52  thf('110', plain,
% 10.31/10.52      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['108', '109'])).
% 10.31/10.52  thf('111', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('demod', [status(thm)], ['4', '9'])).
% 10.31/10.52  thf('112', plain,
% 10.31/10.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 10.31/10.52          | ~ (v13_waybel_0 @ X27 @ X28)
% 10.31/10.52          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 10.31/10.52          | (r2_hidden @ X29 @ X27)
% 10.31/10.52          | ~ (r1_orders_2 @ X28 @ X30 @ X29)
% 10.31/10.52          | ~ (r2_hidden @ X30 @ X27)
% 10.31/10.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 10.31/10.52          | ~ (l1_orders_2 @ X28))),
% 10.31/10.52      inference('cnf', [status(esa)], [d20_waybel_0])).
% 10.31/10.52  thf('113', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (r1_orders_2 @ X0 @ X1 @ X2)
% 10.31/10.52          | (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['111', '112'])).
% 10.31/10.52  thf('114', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 10.31/10.52           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 10.31/10.52           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (l1_orders_2 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['110', '113'])).
% 10.31/10.52  thf('115', plain,
% 10.31/10.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['106', '107'])).
% 10.31/10.52  thf('116', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('117', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 10.31/10.52           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['114', '115', '116'])).
% 10.31/10.52  thf('118', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (l1_orders_2 @ sk_A)
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 10.31/10.52           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['105', '117'])).
% 10.31/10.52  thf('119', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('120', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 10.31/10.52           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['118', '119'])).
% 10.31/10.52  thf('121', plain,
% 10.31/10.52      (((~ (l1_orders_2 @ sk_A)
% 10.31/10.52         | (v2_struct_0 @ sk_A)
% 10.31/10.52         | ~ (v5_orders_2 @ sk_A)
% 10.31/10.52         | ~ (v1_yellow_0 @ sk_A)
% 10.31/10.52         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52              (u1_struct_0 @ sk_A))
% 10.31/10.52         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52            (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['104', '120'])).
% 10.31/10.52  thf('122', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('123', plain, ((v5_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('124', plain, ((v1_yellow_0 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('125', plain,
% 10.31/10.52      ((((v2_struct_0 @ sk_A)
% 10.31/10.52         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52              (u1_struct_0 @ sk_A))
% 10.31/10.52         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52            (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 10.31/10.52  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('127', plain,
% 10.31/10.52      ((((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A))
% 10.31/10.52         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52              (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('clc', [status(thm)], ['125', '126'])).
% 10.31/10.52  thf('128', plain,
% 10.31/10.52      (((~ (l1_orders_2 @ sk_A)
% 10.31/10.52         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 10.31/10.52            (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['81', '127'])).
% 10.31/10.52  thf('129', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('130', plain,
% 10.31/10.52      (((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['128', '129'])).
% 10.31/10.52  thf('131', plain,
% 10.31/10.52      (![X24 : $i, X25 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X24)
% 10.31/10.52          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 10.31/10.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 10.31/10.52  thf('132', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (r1_orders_2 @ X0 @ X1 @ X2)
% 10.31/10.52          | (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['111', '112'])).
% 10.31/10.52  thf('133', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 10.31/10.52          | ~ (r2_hidden @ (k1_yellow_0 @ X0 @ X1) @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['131', '132'])).
% 10.31/10.52  thf('134', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.52         (~ (r2_hidden @ (k1_yellow_0 @ X0 @ X1) @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 10.31/10.52          | (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.31/10.52          | ~ (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['133'])).
% 10.31/10.52  thf('135', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (l1_orders_2 @ sk_A)
% 10.31/10.52           | ~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 10.31/10.52           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ X0)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['130', '134'])).
% 10.31/10.52  thf('136', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('137', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 10.31/10.52           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ X0)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['135', '136'])).
% 10.31/10.52  thf('138', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (l1_orders_2 @ sk_A)
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ X0)
% 10.31/10.52           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['80', '137'])).
% 10.31/10.52  thf('139', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('140', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ X0)
% 10.31/10.52           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['138', '139'])).
% 10.31/10.52  thf('141', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          ((v2_struct_0 @ sk_A)
% 10.31/10.52           | ~ (v5_orders_2 @ sk_A)
% 10.31/10.52           | ~ (v1_yellow_0 @ sk_A)
% 10.31/10.52           | ~ (l1_orders_2 @ sk_A)
% 10.31/10.52           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['64', '140'])).
% 10.31/10.52  thf('142', plain, ((v5_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('143', plain, ((v1_yellow_0 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('144', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('145', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          ((v2_struct_0 @ sk_A)
% 10.31/10.52           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 10.31/10.52  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('147', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('clc', [status(thm)], ['145', '146'])).
% 10.31/10.52  thf('148', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (l1_orders_2 @ sk_A)
% 10.31/10.52           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['47', '147'])).
% 10.31/10.52  thf('149', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('150', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['148', '149'])).
% 10.31/10.52  thf('151', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 10.31/10.52      inference('sup-', [status(thm)], ['18', '19'])).
% 10.31/10.52  thf('152', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['150', '151'])).
% 10.31/10.52  thf('153', plain,
% 10.31/10.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('154', plain,
% 10.31/10.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 10.31/10.52          | ~ (v13_waybel_0 @ X27 @ X28)
% 10.31/10.52          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 10.31/10.52          | (r2_hidden @ X29 @ X27)
% 10.31/10.52          | ~ (r1_orders_2 @ X28 @ X30 @ X29)
% 10.31/10.52          | ~ (r2_hidden @ X30 @ X27)
% 10.31/10.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 10.31/10.52          | ~ (l1_orders_2 @ X28))),
% 10.31/10.52      inference('cnf', [status(esa)], [d20_waybel_0])).
% 10.31/10.52  thf('155', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ sk_A)
% 10.31/10.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 10.31/10.52          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 10.31/10.52          | (r2_hidden @ X1 @ sk_B_2)
% 10.31/10.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (v13_waybel_0 @ sk_B_2 @ sk_A))),
% 10.31/10.52      inference('sup-', [status(thm)], ['153', '154'])).
% 10.31/10.52  thf('156', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('157', plain, ((v13_waybel_0 @ sk_B_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('158', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 10.31/10.52          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 10.31/10.52          | (r2_hidden @ X1 @ sk_B_2)
% 10.31/10.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('demod', [status(thm)], ['155', '156', '157'])).
% 10.31/10.52  thf('159', plain,
% 10.31/10.52      ((![X0 : $i, X1 : $i]:
% 10.31/10.52          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ X1 @ sk_B_2)
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 10.31/10.52           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['152', '158'])).
% 10.31/10.52  thf('160', plain,
% 10.31/10.52      (![X19 : $i]:
% 10.31/10.52         (((k3_yellow_0 @ X19) = (k1_yellow_0 @ X19 @ k1_xboole_0))
% 10.31/10.52          | ~ (l1_orders_2 @ X19))),
% 10.31/10.52      inference('cnf', [status(esa)], [d11_yellow_0])).
% 10.31/10.52  thf('161', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 10.31/10.52           (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | (v2_struct_0 @ X0))),
% 10.31/10.52      inference('simplify', [status(thm)], ['63'])).
% 10.31/10.52  thf('162', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v2_struct_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | ~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0))),
% 10.31/10.52      inference('sup+', [status(thm)], ['160', '161'])).
% 10.31/10.52  thf('163', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (v1_yellow_0 @ X0)
% 10.31/10.52          | ~ (v5_orders_2 @ X0)
% 10.31/10.52          | (v2_struct_0 @ X0)
% 10.31/10.52          | ~ (l1_orders_2 @ X0)
% 10.31/10.52          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 10.31/10.52      inference('simplify', [status(thm)], ['162'])).
% 10.31/10.52  thf('164', plain,
% 10.31/10.52      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['108', '109'])).
% 10.31/10.52  thf('165', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 10.31/10.52          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 10.31/10.52          | (r2_hidden @ X1 @ sk_B_2)
% 10.31/10.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('demod', [status(thm)], ['155', '156', '157'])).
% 10.31/10.52  thf('166', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ X0 @ sk_B_2)
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 10.31/10.52           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['164', '165'])).
% 10.31/10.52  thf('167', plain,
% 10.31/10.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('split', [status(esa)], ['0'])).
% 10.31/10.52  thf('168', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ X0 @ sk_B_2)
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['166', '167'])).
% 10.31/10.52  thf('169', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (~ (l1_orders_2 @ sk_A)
% 10.31/10.52           | (v2_struct_0 @ sk_A)
% 10.31/10.52           | ~ (v5_orders_2 @ sk_A)
% 10.31/10.52           | ~ (v1_yellow_0 @ sk_A)
% 10.31/10.52           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2)
% 10.31/10.52           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['163', '168'])).
% 10.31/10.52  thf('170', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('171', plain, ((v5_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('172', plain, ((v1_yellow_0 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('173', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['150', '151'])).
% 10.31/10.52  thf('174', plain,
% 10.31/10.52      ((![X0 : $i]:
% 10.31/10.52          ((v2_struct_0 @ sk_A)
% 10.31/10.52           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 10.31/10.52  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('176', plain,
% 10.31/10.52      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('clc', [status(thm)], ['174', '175'])).
% 10.31/10.52  thf('177', plain,
% 10.31/10.52      ((![X0 : $i, X1 : $i]:
% 10.31/10.52          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 10.31/10.52           | (r2_hidden @ X1 @ sk_B_2)
% 10.31/10.52           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('demod', [status(thm)], ['159', '176'])).
% 10.31/10.52  thf('178', plain,
% 10.31/10.52      (((((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52         | (r2_hidden @ 
% 10.31/10.52            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52            sk_B_2)
% 10.31/10.52         | ~ (m1_subset_1 @ 
% 10.31/10.52              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52              (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['46', '177'])).
% 10.31/10.52  thf('179', plain,
% 10.31/10.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('180', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 10.31/10.52      inference('demod', [status(thm)], ['4', '9'])).
% 10.31/10.52  thf('181', plain,
% 10.31/10.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 10.31/10.52          | ((X8) = (X6))
% 10.31/10.52          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 10.31/10.52          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 10.31/10.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 10.31/10.52      inference('cnf', [status(esa)], [t8_subset_1])).
% 10.31/10.52  thf('182', plain,
% 10.31/10.52      (![X0 : $i, X1 : $i]:
% 10.31/10.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 10.31/10.52          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 10.31/10.52          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 10.31/10.52          | ((X1) = (X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['180', '181'])).
% 10.31/10.52  thf('183', plain,
% 10.31/10.52      ((((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52        | ~ (r2_hidden @ 
% 10.31/10.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52             sk_B_2)
% 10.31/10.52        | ~ (r2_hidden @ 
% 10.31/10.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52             (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['179', '182'])).
% 10.31/10.52  thf('184', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 10.31/10.52      inference('sup-', [status(thm)], ['14', '15'])).
% 10.31/10.52  thf('185', plain,
% 10.31/10.52      ((~ (r2_hidden @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52           sk_B_2)
% 10.31/10.52        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('clc', [status(thm)], ['183', '184'])).
% 10.31/10.52  thf('186', plain,
% 10.31/10.52      (((~ (m1_subset_1 @ 
% 10.31/10.52            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52            (u1_struct_0 @ sk_A))
% 10.31/10.52         | ((sk_B_2) = (u1_struct_0 @ sk_A))))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('clc', [status(thm)], ['178', '185'])).
% 10.31/10.52  thf('187', plain,
% 10.31/10.52      ((((sk_B_2) = (u1_struct_0 @ sk_A))
% 10.31/10.52        | (m1_subset_1 @ 
% 10.31/10.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 10.31/10.52           (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['17', '20'])).
% 10.31/10.52  thf('188', plain,
% 10.31/10.52      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('clc', [status(thm)], ['186', '187'])).
% 10.31/10.52  thf('189', plain,
% 10.31/10.52      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)
% 10.31/10.52        | (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('190', plain,
% 10.31/10.52      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('split', [status(esa)], ['189'])).
% 10.31/10.52  thf('191', plain,
% 10.31/10.52      (((v1_subset_1 @ sk_B_2 @ sk_B_2))
% 10.31/10.52         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 10.31/10.52             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('sup+', [status(thm)], ['188', '190'])).
% 10.31/10.52  thf('192', plain, (![X9 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X9) @ X9)),
% 10.31/10.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 10.31/10.52  thf('193', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (X0))),
% 10.31/10.52      inference('clc', [status(thm)], ['7', '8'])).
% 10.31/10.52  thf('194', plain, (![X9 : $i]: ~ (v1_subset_1 @ X9 @ X9)),
% 10.31/10.52      inference('demod', [status(thm)], ['192', '193'])).
% 10.31/10.52  thf('195', plain,
% 10.31/10.52      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)) | 
% 10.31/10.52       ~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['191', '194'])).
% 10.31/10.52  thf('196', plain,
% 10.31/10.52      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)) | 
% 10.31/10.52       ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('split', [status(esa)], ['189'])).
% 10.31/10.52  thf('197', plain,
% 10.31/10.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('198', plain,
% 10.31/10.52      (![X31 : $i, X32 : $i]:
% 10.31/10.52         (((X32) = (X31))
% 10.31/10.52          | (v1_subset_1 @ X32 @ X31)
% 10.31/10.52          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 10.31/10.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 10.31/10.52  thf('199', plain,
% 10.31/10.52      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 10.31/10.52        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['197', '198'])).
% 10.31/10.52  thf('200', plain,
% 10.31/10.52      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('split', [status(esa)], ['0'])).
% 10.31/10.52  thf('201', plain,
% 10.31/10.52      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('sup-', [status(thm)], ['199', '200'])).
% 10.31/10.52  thf('202', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('simplify', [status(thm)], ['86'])).
% 10.31/10.52  thf('203', plain,
% 10.31/10.52      (![X10 : $i, X11 : $i]:
% 10.31/10.52         ((r2_hidden @ X10 @ X11)
% 10.31/10.52          | (v1_xboole_0 @ X11)
% 10.31/10.52          | ~ (m1_subset_1 @ X10 @ X11))),
% 10.31/10.52      inference('cnf', [status(esa)], [t2_subset])).
% 10.31/10.52  thf('204', plain,
% 10.31/10.52      (![X0 : $i]:
% 10.31/10.52         (~ (l1_orders_2 @ X0)
% 10.31/10.52          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 10.31/10.52          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['202', '203'])).
% 10.31/10.52  thf('205', plain,
% 10.31/10.52      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)
% 10.31/10.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 10.31/10.52         | ~ (l1_orders_2 @ sk_A)))
% 10.31/10.52         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('sup+', [status(thm)], ['201', '204'])).
% 10.31/10.52  thf('206', plain,
% 10.31/10.52      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 10.31/10.52         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('sup-', [status(thm)], ['199', '200'])).
% 10.31/10.52  thf('207', plain, ((l1_orders_2 @ sk_A)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('208', plain,
% 10.31/10.52      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2) | (v1_xboole_0 @ sk_B_2)))
% 10.31/10.52         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('demod', [status(thm)], ['205', '206', '207'])).
% 10.31/10.52  thf('209', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 10.31/10.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.52  thf('210', plain,
% 10.31/10.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 10.31/10.52         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 10.31/10.52      inference('clc', [status(thm)], ['208', '209'])).
% 10.31/10.52  thf('211', plain,
% 10.31/10.52      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 10.31/10.52         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 10.31/10.52      inference('split', [status(esa)], ['189'])).
% 10.31/10.52  thf('212', plain,
% 10.31/10.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)) | 
% 10.31/10.52       ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.52      inference('sup-', [status(thm)], ['210', '211'])).
% 10.31/10.52  thf('213', plain, ($false),
% 10.31/10.52      inference('sat_resolution*', [status(thm)], ['1', '195', '196', '212'])).
% 10.31/10.52  
% 10.31/10.52  % SZS output end Refutation
% 10.31/10.52  
% 10.31/10.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
