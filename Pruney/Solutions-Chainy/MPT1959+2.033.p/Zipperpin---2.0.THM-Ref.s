%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RuabLeXI9h

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:14 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 419 expanded)
%              Number of leaves         :   39 ( 137 expanded)
%              Depth                    :   26
%              Number of atoms          : 1610 (6220 expanded)
%              Number of equality atoms :   36 (  74 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X19: $i] :
      ( ( r1_yellow_0 @ X19 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v1_yellow_0 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('5',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( X5 = X3 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_lattice3 @ X21 @ k1_xboole_0 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('15',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ),
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

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k1_yellow_0 @ X13 @ X14 ) )
      | ~ ( r2_lattice3 @ X13 @ X14 @ X16 )
      | ( r1_orders_2 @ X13 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_yellow_0 @ X13 @ X14 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( r1_yellow_0 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ ( k1_yellow_0 @ X13 @ X14 ) @ X16 )
      | ~ ( r2_lattice3 @ X13 @ X14 @ X16 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','28'])).

thf('30',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X12: $i] :
      ( ( ( k3_yellow_0 @ X12 )
        = ( k1_yellow_0 @ X12 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('38',plain,(
    ! [X19: $i] :
      ( ( r1_yellow_0 @ X19 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v1_yellow_0 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_lattice3 @ X21 @ k1_xboole_0 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
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

thf('63',plain,(
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

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','70'])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('86',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('88',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('92',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('96',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['89','96'])).

thf('98',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('99',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['100'])).

thf('102',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['99','101'])).

thf('103',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('105',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ X6 @ X6 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['100'])).

thf('108',plain,(
    ! [X12: $i] :
      ( ( ( k3_yellow_0 @ X12 )
        = ( k1_yellow_0 @ X12 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('109',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('111',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['108','117'])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('121',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['100'])).

thf('126',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','106','107','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RuabLeXI9h
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 444 iterations in 0.265s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.49/0.72  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.49/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.72  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.49/0.72  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.49/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.49/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.72  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.49/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.49/0.72  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.49/0.72  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.49/0.72  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.49/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.49/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.72  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.49/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.72  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.49/0.72  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.49/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.72  thf(t8_waybel_7, conjecture,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.49/0.72         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.49/0.72         ( l1_orders_2 @ A ) ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.49/0.72             ( v13_waybel_0 @ B @ A ) & 
% 0.49/0.72             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.72           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.49/0.72             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i]:
% 0.49/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.49/0.72            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.49/0.72            ( l1_orders_2 @ A ) ) =>
% 0.49/0.72          ( ![B:$i]:
% 0.49/0.72            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.49/0.72                ( v13_waybel_0 @ B @ A ) & 
% 0.49/0.72                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.72              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.49/0.72                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.49/0.72  thf('0', plain,
% 0.49/0.72      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.49/0.72        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.49/0.72       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf(t42_yellow_0, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.49/0.72         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.49/0.72       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.49/0.72         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.49/0.72  thf('2', plain,
% 0.49/0.72      (![X19 : $i]:
% 0.49/0.72         ((r1_yellow_0 @ X19 @ k1_xboole_0)
% 0.49/0.72          | ~ (l1_orders_2 @ X19)
% 0.49/0.72          | ~ (v1_yellow_0 @ X19)
% 0.49/0.72          | ~ (v5_orders_2 @ X19)
% 0.49/0.72          | (v2_struct_0 @ X19))),
% 0.49/0.72      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(rc3_subset_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ?[B:$i]:
% 0.49/0.72       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.49/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.49/0.72      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.49/0.72  thf('5', plain,
% 0.49/0.72      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.49/0.72      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.49/0.72  thf(d7_subset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.72       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      (![X26 : $i, X27 : $i]:
% 0.49/0.72         (((X27) = (X26))
% 0.49/0.72          | (v1_subset_1 @ X27 @ X26)
% 0.49/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.49/0.72      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.49/0.72  thf('7', plain,
% 0.49/0.72      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.72  thf('8', plain, (![X6 : $i]: ~ (v1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.49/0.72      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.49/0.72  thf('9', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.49/0.72      inference('clc', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('10', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.49/0.72      inference('demod', [status(thm)], ['4', '9'])).
% 0.49/0.72  thf(t8_subset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.72       ( ![C:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.72           ( ( ![D:$i]:
% 0.49/0.72               ( ( m1_subset_1 @ D @ A ) =>
% 0.49/0.72                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.49/0.72             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.49/0.72  thf('11', plain,
% 0.49/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.49/0.72          | ((X5) = (X3))
% 0.49/0.72          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 0.49/0.72          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.72          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.49/0.72          | ((X1) = (X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | (m1_subset_1 @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72           (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['3', '12'])).
% 0.49/0.72  thf(t6_yellow_0, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( l1_orders_2 @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.72           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.49/0.72             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      (![X20 : $i, X21 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.49/0.72          | (r2_lattice3 @ X21 @ k1_xboole_0 @ X20)
% 0.49/0.72          | ~ (l1_orders_2 @ X21))),
% 0.49/0.72      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | ~ (l1_orders_2 @ sk_A)
% 0.49/0.72        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.72  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('17', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.49/0.72  thf('18', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | (m1_subset_1 @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72           (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['3', '12'])).
% 0.49/0.72  thf(dt_k1_yellow_0, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( l1_orders_2 @ A ) =>
% 0.49/0.72       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.49/0.72  thf('19', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X17)
% 0.49/0.72          | (m1_subset_1 @ (k1_yellow_0 @ X17 @ X18) @ (u1_struct_0 @ X17)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.49/0.72  thf(d9_yellow_0, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( l1_orders_2 @ A ) =>
% 0.49/0.72       ( ![B:$i,C:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.72           ( ( r1_yellow_0 @ A @ B ) =>
% 0.49/0.72             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.49/0.72               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.49/0.72                 ( ![D:$i]:
% 0.49/0.72                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.72                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.49/0.72                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.72         (((X15) != (k1_yellow_0 @ X13 @ X14))
% 0.49/0.72          | ~ (r2_lattice3 @ X13 @ X14 @ X16)
% 0.49/0.72          | (r1_orders_2 @ X13 @ X15 @ X16)
% 0.49/0.72          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.49/0.72          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.49/0.72          | ~ (r1_yellow_0 @ X13 @ X14)
% 0.49/0.72          | ~ (l1_orders_2 @ X13))),
% 0.49/0.72      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.49/0.72  thf('21', plain,
% 0.49/0.72      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X13)
% 0.49/0.72          | ~ (r1_yellow_0 @ X13 @ X14)
% 0.49/0.72          | ~ (m1_subset_1 @ (k1_yellow_0 @ X13 @ X14) @ (u1_struct_0 @ X13))
% 0.49/0.72          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.49/0.72          | (r1_orders_2 @ X13 @ (k1_yellow_0 @ X13 @ X14) @ X16)
% 0.49/0.72          | ~ (r2_lattice3 @ X13 @ X14 @ X16))),
% 0.49/0.72      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.72  thf('22', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X0)
% 0.49/0.72          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.49/0.72          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.49/0.72          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.72          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.49/0.72          | ~ (l1_orders_2 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['19', '21'])).
% 0.49/0.72  thf('23', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (r1_yellow_0 @ X0 @ X1)
% 0.49/0.72          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.72          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.49/0.72          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.49/0.72          | ~ (l1_orders_2 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['22'])).
% 0.49/0.72  thf('24', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72          | ~ (l1_orders_2 @ sk_A)
% 0.49/0.72          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.49/0.72               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.49/0.72             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['18', '23'])).
% 0.49/0.72  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('26', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.49/0.72               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.49/0.72             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['24', '25'])).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.49/0.72        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['17', '26'])).
% 0.49/0.72  thf('28', plain,
% 0.49/0.72      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.49/0.72         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.49/0.72        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['27'])).
% 0.49/0.72  thf('29', plain,
% 0.49/0.72      (((v2_struct_0 @ sk_A)
% 0.49/0.72        | ~ (v5_orders_2 @ sk_A)
% 0.49/0.72        | ~ (v1_yellow_0 @ sk_A)
% 0.49/0.72        | ~ (l1_orders_2 @ sk_A)
% 0.49/0.72        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['2', '28'])).
% 0.49/0.72  thf('30', plain, ((v5_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('31', plain, ((v1_yellow_0 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('33', plain,
% 0.49/0.72      (((v2_struct_0 @ sk_A)
% 0.49/0.72        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.49/0.72  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('35', plain,
% 0.49/0.72      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.49/0.72         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('clc', [status(thm)], ['33', '34'])).
% 0.49/0.72  thf('36', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X17)
% 0.49/0.72          | (m1_subset_1 @ (k1_yellow_0 @ X17 @ X18) @ (u1_struct_0 @ X17)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.49/0.72  thf(d11_yellow_0, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( l1_orders_2 @ A ) =>
% 0.49/0.72       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.49/0.72  thf('37', plain,
% 0.49/0.72      (![X12 : $i]:
% 0.49/0.72         (((k3_yellow_0 @ X12) = (k1_yellow_0 @ X12 @ k1_xboole_0))
% 0.49/0.72          | ~ (l1_orders_2 @ X12))),
% 0.49/0.72      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.49/0.72  thf('38', plain,
% 0.49/0.72      (![X19 : $i]:
% 0.49/0.72         ((r1_yellow_0 @ X19 @ k1_xboole_0)
% 0.49/0.72          | ~ (l1_orders_2 @ X19)
% 0.49/0.72          | ~ (v1_yellow_0 @ X19)
% 0.49/0.72          | ~ (v5_orders_2 @ X19)
% 0.49/0.72          | (v2_struct_0 @ X19))),
% 0.49/0.72      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.49/0.72  thf('39', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X17)
% 0.49/0.72          | (m1_subset_1 @ (k1_yellow_0 @ X17 @ X18) @ (u1_struct_0 @ X17)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.49/0.72  thf('40', plain,
% 0.49/0.72      (![X20 : $i, X21 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.49/0.72          | (r2_lattice3 @ X21 @ k1_xboole_0 @ X20)
% 0.49/0.72          | ~ (l1_orders_2 @ X21))),
% 0.49/0.72      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X0)
% 0.49/0.72          | ~ (l1_orders_2 @ X0)
% 0.49/0.72          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.72  thf('42', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1))
% 0.49/0.72          | ~ (l1_orders_2 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['41'])).
% 0.49/0.72  thf('43', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X17)
% 0.49/0.72          | (m1_subset_1 @ (k1_yellow_0 @ X17 @ X18) @ (u1_struct_0 @ X17)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.49/0.72  thf('44', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (r1_yellow_0 @ X0 @ X1)
% 0.49/0.72          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.72          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.49/0.72          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.49/0.72          | ~ (l1_orders_2 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['22'])).
% 0.49/0.72  thf('45', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X0)
% 0.49/0.72          | ~ (l1_orders_2 @ X0)
% 0.49/0.72          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.49/0.72          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.49/0.72             (k1_yellow_0 @ X0 @ X1))
% 0.49/0.72          | ~ (r1_yellow_0 @ X0 @ X2))),
% 0.49/0.72      inference('sup-', [status(thm)], ['43', '44'])).
% 0.49/0.72  thf('46', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (r1_yellow_0 @ X0 @ X2)
% 0.49/0.72          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.49/0.72             (k1_yellow_0 @ X0 @ X1))
% 0.49/0.72          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.49/0.72          | ~ (l1_orders_2 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['45'])).
% 0.49/0.72  thf('47', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X1)
% 0.49/0.72          | ~ (l1_orders_2 @ X1)
% 0.49/0.72          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.49/0.72             (k1_yellow_0 @ X1 @ X0))
% 0.49/0.72          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['42', '46'])).
% 0.49/0.72  thf('48', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 0.49/0.72          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.49/0.72             (k1_yellow_0 @ X1 @ X0))
% 0.49/0.72          | ~ (l1_orders_2 @ X1))),
% 0.49/0.72      inference('simplify', [status(thm)], ['47'])).
% 0.49/0.72  thf('49', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((v2_struct_0 @ X0)
% 0.49/0.72          | ~ (v5_orders_2 @ X0)
% 0.49/0.72          | ~ (v1_yellow_0 @ X0)
% 0.49/0.72          | ~ (l1_orders_2 @ X0)
% 0.49/0.72          | ~ (l1_orders_2 @ X0)
% 0.49/0.72          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.49/0.72             (k1_yellow_0 @ X0 @ X1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['38', '48'])).
% 0.49/0.72  thf('50', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.49/0.72           (k1_yellow_0 @ X0 @ X1))
% 0.49/0.72          | ~ (l1_orders_2 @ X0)
% 0.49/0.72          | ~ (v1_yellow_0 @ X0)
% 0.49/0.72          | ~ (v5_orders_2 @ X0)
% 0.49/0.72          | (v2_struct_0 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['49'])).
% 0.49/0.72  thf('51', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.49/0.72          | ~ (l1_orders_2 @ X0)
% 0.49/0.72          | (v2_struct_0 @ X0)
% 0.49/0.72          | ~ (v5_orders_2 @ X0)
% 0.49/0.72          | ~ (v1_yellow_0 @ X0)
% 0.49/0.72          | ~ (l1_orders_2 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['37', '50'])).
% 0.49/0.72  thf('52', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (v1_yellow_0 @ X0)
% 0.49/0.72          | ~ (v5_orders_2 @ X0)
% 0.49/0.72          | (v2_struct_0 @ X0)
% 0.49/0.72          | ~ (l1_orders_2 @ X0)
% 0.49/0.72          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['51'])).
% 0.49/0.72  thf('53', plain,
% 0.49/0.72      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('54', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(l3_subset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.49/0.72  thf('55', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.49/0.72          | (r2_hidden @ X0 @ X2)
% 0.49/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.49/0.72      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.49/0.72  thf('56', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['54', '55'])).
% 0.49/0.72  thf('57', plain,
% 0.49/0.72      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['53', '56'])).
% 0.49/0.72  thf('58', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.49/0.72      inference('demod', [status(thm)], ['4', '9'])).
% 0.49/0.72  thf(t4_subset, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.49/0.72       ( m1_subset_1 @ A @ C ) ))).
% 0.49/0.72  thf('59', plain,
% 0.49/0.72      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ X10)
% 0.49/0.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.49/0.72          | (m1_subset_1 @ X9 @ X11))),
% 0.49/0.72      inference('cnf', [status(esa)], [t4_subset])).
% 0.49/0.72  thf('60', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['58', '59'])).
% 0.49/0.72  thf('61', plain,
% 0.49/0.72      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['57', '60'])).
% 0.49/0.72  thf('62', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(d20_waybel_0, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( l1_orders_2 @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.49/0.72             ( ![C:$i]:
% 0.49/0.72               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.72                 ( ![D:$i]:
% 0.49/0.72                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.72                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.49/0.72                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.72  thf('63', plain,
% 0.49/0.72      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.49/0.72          | ~ (v13_waybel_0 @ X22 @ X23)
% 0.49/0.72          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.49/0.72          | (r2_hidden @ X24 @ X22)
% 0.49/0.72          | ~ (r1_orders_2 @ X23 @ X25 @ X24)
% 0.49/0.72          | ~ (r2_hidden @ X25 @ X22)
% 0.49/0.72          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.49/0.72          | ~ (l1_orders_2 @ X23))),
% 0.49/0.72      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.49/0.72  thf('64', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ sk_A)
% 0.49/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.72          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.49/0.72          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.49/0.72          | (r2_hidden @ X1 @ sk_B_1)
% 0.49/0.72          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.49/0.72          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.72  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('66', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('67', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.72          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.49/0.72          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.49/0.72          | (r2_hidden @ X1 @ sk_B_1)
% 0.49/0.72          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.49/0.72  thf('68', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.72           | (r2_hidden @ X0 @ sk_B_1)
% 0.49/0.72           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.49/0.72           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['61', '67'])).
% 0.49/0.72  thf('69', plain,
% 0.49/0.72      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('70', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.72           | (r2_hidden @ X0 @ sk_B_1)
% 0.49/0.72           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['68', '69'])).
% 0.49/0.72  thf('71', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (~ (l1_orders_2 @ sk_A)
% 0.49/0.72           | (v2_struct_0 @ sk_A)
% 0.49/0.72           | ~ (v5_orders_2 @ sk_A)
% 0.49/0.72           | ~ (v1_yellow_0 @ sk_A)
% 0.49/0.72           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.49/0.72           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['52', '70'])).
% 0.49/0.72  thf('72', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('73', plain, ((v5_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('74', plain, ((v1_yellow_0 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('75', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          ((v2_struct_0 @ sk_A)
% 0.49/0.72           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.49/0.72           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.49/0.72  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('77', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.49/0.72           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('clc', [status(thm)], ['75', '76'])).
% 0.49/0.72  thf('78', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (~ (l1_orders_2 @ sk_A)
% 0.49/0.72           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['36', '77'])).
% 0.49/0.72  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('80', plain,
% 0.49/0.72      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['78', '79'])).
% 0.49/0.72  thf('81', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('82', plain,
% 0.49/0.72      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ X10)
% 0.49/0.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.49/0.72          | (m1_subset_1 @ X9 @ X11))),
% 0.49/0.72      inference('cnf', [status(esa)], [t4_subset])).
% 0.49/0.72  thf('83', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.72          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.72  thf('84', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['80', '83'])).
% 0.49/0.72  thf('85', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.72          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.49/0.72          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.49/0.72          | (r2_hidden @ X1 @ sk_B_1)
% 0.49/0.72          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.49/0.72  thf('86', plain,
% 0.49/0.72      ((![X0 : $i, X1 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.49/0.72           | (r2_hidden @ X1 @ sk_B_1)
% 0.49/0.72           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.49/0.72           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['84', '85'])).
% 0.49/0.72  thf('87', plain,
% 0.49/0.72      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['78', '79'])).
% 0.49/0.72  thf('88', plain,
% 0.49/0.72      ((![X0 : $i, X1 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.49/0.72           | (r2_hidden @ X1 @ sk_B_1)
% 0.49/0.72           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['86', '87'])).
% 0.49/0.72  thf('89', plain,
% 0.49/0.72      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72         | (r2_hidden @ 
% 0.49/0.72            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72            sk_B_1)
% 0.49/0.72         | ~ (m1_subset_1 @ 
% 0.49/0.72              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72              (u1_struct_0 @ sk_A))))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['35', '88'])).
% 0.49/0.72  thf('90', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('91', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.49/0.72      inference('demod', [status(thm)], ['4', '9'])).
% 0.49/0.72  thf('92', plain,
% 0.49/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.49/0.72          | ((X5) = (X3))
% 0.49/0.72          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.49/0.72          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.49/0.72          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.49/0.72  thf('93', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.72          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.49/0.72          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.49/0.72          | ((X1) = (X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['91', '92'])).
% 0.49/0.72  thf('94', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | ~ (r2_hidden @ 
% 0.49/0.72             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72             sk_B_1)
% 0.49/0.72        | ~ (r2_hidden @ 
% 0.49/0.72             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72             (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['90', '93'])).
% 0.49/0.72  thf('95', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['54', '55'])).
% 0.49/0.72  thf('96', plain,
% 0.49/0.72      ((~ (r2_hidden @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72           sk_B_1)
% 0.49/0.72        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('clc', [status(thm)], ['94', '95'])).
% 0.49/0.72  thf('97', plain,
% 0.49/0.72      (((~ (m1_subset_1 @ 
% 0.49/0.72            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72            (u1_struct_0 @ sk_A))
% 0.49/0.72         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('clc', [status(thm)], ['89', '96'])).
% 0.49/0.72  thf('98', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.72        | (m1_subset_1 @ 
% 0.49/0.72           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.49/0.72           (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['3', '12'])).
% 0.49/0.72  thf('99', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.49/0.72         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('clc', [status(thm)], ['97', '98'])).
% 0.49/0.72  thf('100', plain,
% 0.49/0.72      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.49/0.72        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('101', plain,
% 0.49/0.72      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('split', [status(esa)], ['100'])).
% 0.49/0.72  thf('102', plain,
% 0.49/0.72      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.49/0.72         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.49/0.72             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['99', '101'])).
% 0.49/0.72  thf('103', plain, (![X6 : $i]: ~ (v1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.49/0.72      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.49/0.72  thf('104', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.49/0.72      inference('clc', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('105', plain, (![X6 : $i]: ~ (v1_subset_1 @ X6 @ X6)),
% 0.49/0.72      inference('demod', [status(thm)], ['103', '104'])).
% 0.49/0.72  thf('106', plain,
% 0.49/0.72      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.49/0.72       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['102', '105'])).
% 0.49/0.72  thf('107', plain,
% 0.49/0.72      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.49/0.72       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['100'])).
% 0.49/0.72  thf('108', plain,
% 0.49/0.72      (![X12 : $i]:
% 0.49/0.72         (((k3_yellow_0 @ X12) = (k1_yellow_0 @ X12 @ k1_xboole_0))
% 0.49/0.72          | ~ (l1_orders_2 @ X12))),
% 0.49/0.72      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.49/0.72  thf('109', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('110', plain,
% 0.49/0.72      (![X26 : $i, X27 : $i]:
% 0.49/0.72         (((X27) = (X26))
% 0.49/0.72          | (v1_subset_1 @ X27 @ X26)
% 0.49/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.49/0.72      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.49/0.72  thf('111', plain,
% 0.49/0.72      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.49/0.72        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['109', '110'])).
% 0.49/0.72  thf('112', plain,
% 0.49/0.72      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('113', plain,
% 0.49/0.72      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.49/0.72         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['111', '112'])).
% 0.49/0.72  thf('114', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i]:
% 0.49/0.72         (~ (l1_orders_2 @ X17)
% 0.49/0.72          | (m1_subset_1 @ (k1_yellow_0 @ X17 @ X18) @ (u1_struct_0 @ X17)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.49/0.72  thf('115', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.49/0.72           | ~ (l1_orders_2 @ sk_A)))
% 0.49/0.72         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('sup+', [status(thm)], ['113', '114'])).
% 0.49/0.72  thf('116', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('117', plain,
% 0.49/0.72      ((![X0 : $i]: (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.49/0.72         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('demod', [status(thm)], ['115', '116'])).
% 0.49/0.72  thf('118', plain,
% 0.49/0.72      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1) | ~ (l1_orders_2 @ sk_A)))
% 0.49/0.72         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('sup+', [status(thm)], ['108', '117'])).
% 0.49/0.72  thf('119', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('120', plain,
% 0.49/0.72      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.49/0.72         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('demod', [status(thm)], ['118', '119'])).
% 0.49/0.72  thf(t2_subset, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ A @ B ) =>
% 0.49/0.72       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.49/0.72  thf('121', plain,
% 0.49/0.72      (![X7 : $i, X8 : $i]:
% 0.49/0.72         ((r2_hidden @ X7 @ X8)
% 0.49/0.72          | (v1_xboole_0 @ X8)
% 0.49/0.72          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.49/0.72      inference('cnf', [status(esa)], [t2_subset])).
% 0.49/0.72  thf('122', plain,
% 0.49/0.72      ((((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.49/0.72         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['120', '121'])).
% 0.49/0.72  thf('123', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('124', plain,
% 0.49/0.72      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.49/0.72         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('clc', [status(thm)], ['122', '123'])).
% 0.49/0.72  thf('125', plain,
% 0.49/0.72      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.49/0.72         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.49/0.72      inference('split', [status(esa)], ['100'])).
% 0.49/0.72  thf('126', plain,
% 0.49/0.72      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.49/0.72       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['124', '125'])).
% 0.49/0.72  thf('127', plain, ($false),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['1', '106', '107', '126'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.57/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
