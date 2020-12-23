%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K7N1NQzEbv

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:14 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 585 expanded)
%              Number of leaves         :   36 ( 174 expanded)
%              Depth                    :   29
%              Number of atoms          : 1445 (10194 expanded)
%              Number of equality atoms :   35 (  88 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

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
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X14: $i] :
      ( ( r1_yellow_0 @ X14 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v1_yellow_0 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_lattice3 @ X16 @ k1_xboole_0 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('7',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
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

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k1_yellow_0 @ X8 @ X9 ) )
      | ~ ( r2_lattice3 @ X8 @ X9 @ X11 )
      | ( r1_orders_2 @ X8 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_yellow_0 @ X8 @ X9 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( r1_yellow_0 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ ( k1_yellow_0 @ X8 @ X9 ) @ X11 )
      | ~ ( r2_lattice3 @ X8 @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( ( ( k3_yellow_0 @ X7 )
        = ( k1_yellow_0 @ X7 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('30',plain,(
    ! [X14: $i] :
      ( ( r1_yellow_0 @ X14 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v1_yellow_0 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_lattice3 @ X16 @ k1_xboole_0 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('51',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X19 @ X17 )
      | ~ ( r1_orders_2 @ X18 @ X20 @ X19 )
      | ~ ( r2_hidden @ X20 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','65'])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('74',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','74'])).

thf('76',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('77',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('79',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','84'])).

thf('86',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('89',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_subset_1 @ X22 @ X21 )
      | ( X22 != X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('90',plain,(
    ! [X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( v1_subset_1 @ X21 @ X21 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( v1_subset_1 @ sk_B @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['83'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 = X21 )
      | ( v1_subset_1 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('96',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X7: $i] :
      ( ( ( k3_yellow_0 @ X7 )
        = ( k1_yellow_0 @ X7 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('100',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['98','104'])).

thf('106',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['83'])).

thf('112',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','92','93','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K7N1NQzEbv
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:26:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 285 iterations in 0.163s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.44/0.63  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.44/0.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.44/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.63  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.44/0.63  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.44/0.63  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.44/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.63  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.44/0.63  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.44/0.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.44/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.63  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.44/0.63  thf(t8_waybel_7, conjecture,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.44/0.63         ( l1_orders_2 @ A ) ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.44/0.63             ( v13_waybel_0 @ B @ A ) & 
% 0.44/0.63             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.63           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.44/0.63             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i]:
% 0.44/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.63            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.44/0.63            ( l1_orders_2 @ A ) ) =>
% 0.44/0.63          ( ![B:$i]:
% 0.44/0.63            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.44/0.63                ( v13_waybel_0 @ B @ A ) & 
% 0.44/0.63                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.63              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.44/0.63                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.44/0.63        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.44/0.63       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf(t42_yellow_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.44/0.63         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.63       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.44/0.63         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (![X14 : $i]:
% 0.44/0.63         ((r1_yellow_0 @ X14 @ k1_xboole_0)
% 0.44/0.63          | ~ (l1_orders_2 @ X14)
% 0.44/0.63          | ~ (v1_yellow_0 @ X14)
% 0.44/0.63          | ~ (v5_orders_2 @ X14)
% 0.44/0.63          | (v2_struct_0 @ X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.44/0.63  thf('3', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t49_subset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.63       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.44/0.63         ( ( A ) = ( B ) ) ) ))).
% 0.44/0.63  thf('4', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.44/0.63          | ((X1) = (X0))
% 0.44/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.44/0.63  thf('5', plain,
% 0.44/0.63      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.63           (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.63  thf(t6_yellow_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_orders_2 @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.44/0.63             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.44/0.63  thf('6', plain,
% 0.44/0.63      (![X15 : $i, X16 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.44/0.63          | (r2_lattice3 @ X16 @ k1_xboole_0 @ X15)
% 0.44/0.63          | ~ (l1_orders_2 @ X16))),
% 0.44/0.63      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63        | ~ (l1_orders_2 @ sk_A)
% 0.44/0.63        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.44/0.63           (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.63  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.44/0.63           (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.63  thf('10', plain,
% 0.44/0.63      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.63           (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.63  thf(dt_k1_yellow_0, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( l1_orders_2 @ A ) =>
% 0.44/0.63       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.44/0.63  thf('11', plain,
% 0.44/0.63      (![X12 : $i, X13 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X12)
% 0.44/0.63          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.44/0.63  thf(d9_yellow_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_orders_2 @ A ) =>
% 0.44/0.63       ( ![B:$i,C:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63           ( ( r1_yellow_0 @ A @ B ) =>
% 0.44/0.63             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.44/0.63               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.44/0.63                 ( ![D:$i]:
% 0.44/0.63                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.44/0.63                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf('12', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.63         (((X10) != (k1_yellow_0 @ X8 @ X9))
% 0.44/0.63          | ~ (r2_lattice3 @ X8 @ X9 @ X11)
% 0.44/0.63          | (r1_orders_2 @ X8 @ X10 @ X11)
% 0.44/0.63          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.44/0.63          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.44/0.63          | ~ (r1_yellow_0 @ X8 @ X9)
% 0.44/0.63          | ~ (l1_orders_2 @ X8))),
% 0.44/0.63      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X8)
% 0.44/0.63          | ~ (r1_yellow_0 @ X8 @ X9)
% 0.44/0.63          | ~ (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8))
% 0.44/0.63          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.44/0.63          | (r1_orders_2 @ X8 @ (k1_yellow_0 @ X8 @ X9) @ X11)
% 0.44/0.63          | ~ (r2_lattice3 @ X8 @ X9 @ X11))),
% 0.44/0.63      inference('simplify', [status(thm)], ['12'])).
% 0.44/0.63  thf('14', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X0)
% 0.44/0.63          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.44/0.63          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.44/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.44/0.63          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.44/0.63          | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['11', '13'])).
% 0.44/0.63  thf('15', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (~ (r1_yellow_0 @ X0 @ X1)
% 0.44/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.44/0.63          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.44/0.63          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.44/0.63          | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.44/0.63  thf('16', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.63          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.44/0.63             (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['10', '15'])).
% 0.44/0.63  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('18', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.44/0.63             (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.44/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.44/0.63        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.63           (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['9', '18'])).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.63         (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.44/0.63        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['19'])).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      (((v2_struct_0 @ sk_A)
% 0.44/0.63        | ~ (v5_orders_2 @ sk_A)
% 0.44/0.63        | ~ (v1_yellow_0 @ sk_A)
% 0.44/0.63        | ~ (l1_orders_2 @ sk_A)
% 0.44/0.63        | ((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.63           (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['2', '20'])).
% 0.44/0.63  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('23', plain, ((v1_yellow_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('25', plain,
% 0.44/0.63      (((v2_struct_0 @ sk_A)
% 0.44/0.63        | ((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.63           (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.44/0.63  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.63         (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.44/0.63      inference('clc', [status(thm)], ['25', '26'])).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      (![X12 : $i, X13 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X12)
% 0.44/0.63          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.44/0.63  thf(d11_yellow_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_orders_2 @ A ) =>
% 0.44/0.63       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.44/0.63  thf('29', plain,
% 0.44/0.63      (![X7 : $i]:
% 0.44/0.63         (((k3_yellow_0 @ X7) = (k1_yellow_0 @ X7 @ k1_xboole_0))
% 0.44/0.63          | ~ (l1_orders_2 @ X7))),
% 0.44/0.63      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.44/0.63  thf('30', plain,
% 0.44/0.63      (![X14 : $i]:
% 0.44/0.63         ((r1_yellow_0 @ X14 @ k1_xboole_0)
% 0.44/0.63          | ~ (l1_orders_2 @ X14)
% 0.44/0.63          | ~ (v1_yellow_0 @ X14)
% 0.44/0.63          | ~ (v5_orders_2 @ X14)
% 0.44/0.63          | (v2_struct_0 @ X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.44/0.63  thf('31', plain,
% 0.44/0.63      (![X12 : $i, X13 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X12)
% 0.44/0.63          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.44/0.63  thf('32', plain,
% 0.44/0.63      (![X15 : $i, X16 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.44/0.63          | (r2_lattice3 @ X16 @ k1_xboole_0 @ X15)
% 0.44/0.63          | ~ (l1_orders_2 @ X16))),
% 0.44/0.63      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.44/0.63  thf('33', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X0)
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.63  thf('34', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1))
% 0.44/0.63          | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.44/0.63  thf('35', plain,
% 0.44/0.63      (![X12 : $i, X13 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X12)
% 0.44/0.63          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.44/0.63  thf('36', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (~ (r1_yellow_0 @ X0 @ X1)
% 0.44/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.44/0.63          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.44/0.63          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.44/0.63          | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.44/0.63  thf('37', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X0)
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.44/0.63          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.44/0.63             (k1_yellow_0 @ X0 @ X1))
% 0.44/0.63          | ~ (r1_yellow_0 @ X0 @ X2))),
% 0.44/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.63  thf('38', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (~ (r1_yellow_0 @ X0 @ X2)
% 0.44/0.63          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.44/0.63             (k1_yellow_0 @ X0 @ X1))
% 0.44/0.63          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.44/0.63          | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['37'])).
% 0.44/0.63  thf('39', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X1)
% 0.44/0.63          | ~ (l1_orders_2 @ X1)
% 0.44/0.63          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.44/0.63             (k1_yellow_0 @ X1 @ X0))
% 0.44/0.63          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['34', '38'])).
% 0.44/0.63  thf('40', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 0.44/0.63          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.44/0.63             (k1_yellow_0 @ X1 @ X0))
% 0.44/0.63          | ~ (l1_orders_2 @ X1))),
% 0.44/0.63      inference('simplify', [status(thm)], ['39'])).
% 0.44/0.63  thf('41', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((v2_struct_0 @ X0)
% 0.44/0.63          | ~ (v5_orders_2 @ X0)
% 0.44/0.63          | ~ (v1_yellow_0 @ X0)
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.44/0.63             (k1_yellow_0 @ X0 @ X1)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['30', '40'])).
% 0.44/0.63  thf('42', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.44/0.63           (k1_yellow_0 @ X0 @ X1))
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | ~ (v1_yellow_0 @ X0)
% 0.44/0.63          | ~ (v5_orders_2 @ X0)
% 0.44/0.63          | (v2_struct_0 @ X0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.63  thf('43', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | (v2_struct_0 @ X0)
% 0.44/0.63          | ~ (v5_orders_2 @ X0)
% 0.44/0.63          | ~ (v1_yellow_0 @ X0)
% 0.44/0.63          | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['29', '42'])).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (v1_yellow_0 @ X0)
% 0.44/0.63          | ~ (v5_orders_2 @ X0)
% 0.44/0.63          | (v2_struct_0 @ X0)
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['43'])).
% 0.44/0.63  thf('45', plain,
% 0.44/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf('46', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t4_subset, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.44/0.63       ( m1_subset_1 @ A @ C ) ))).
% 0.44/0.63  thf('47', plain,
% 0.44/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X4 @ X5)
% 0.44/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.44/0.63          | (m1_subset_1 @ X4 @ X6))),
% 0.44/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.44/0.63  thf('48', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.44/0.63  thf('49', plain,
% 0.44/0.63      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['45', '48'])).
% 0.44/0.63  thf('50', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(d20_waybel_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_orders_2 @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.44/0.63             ( ![C:$i]:
% 0.44/0.63               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63                 ( ![D:$i]:
% 0.44/0.63                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.44/0.63                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf('51', plain,
% 0.44/0.63      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.44/0.63          | ~ (v13_waybel_0 @ X17 @ X18)
% 0.44/0.63          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.44/0.63          | (r2_hidden @ X19 @ X17)
% 0.44/0.63          | ~ (r1_orders_2 @ X18 @ X20 @ X19)
% 0.44/0.63          | ~ (r2_hidden @ X20 @ X17)
% 0.44/0.63          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.44/0.63          | ~ (l1_orders_2 @ X18))),
% 0.44/0.63      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.44/0.63  thf('52', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ sk_A)
% 0.44/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.63          | ~ (r2_hidden @ X0 @ sk_B)
% 0.44/0.63          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.63          | (r2_hidden @ X1 @ sk_B)
% 0.44/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.44/0.63          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.44/0.63  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('54', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('55', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.63          | ~ (r2_hidden @ X0 @ sk_B)
% 0.44/0.63          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.63          | (r2_hidden @ X1 @ sk_B)
% 0.44/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.44/0.63  thf('56', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.63           | (r2_hidden @ X0 @ sk_B)
% 0.44/0.63           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.44/0.63           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['49', '55'])).
% 0.44/0.63  thf('57', plain,
% 0.44/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf('58', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.63           | (r2_hidden @ X0 @ sk_B)
% 0.44/0.63           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['56', '57'])).
% 0.44/0.63  thf('59', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (~ (l1_orders_2 @ sk_A)
% 0.44/0.63           | (v2_struct_0 @ sk_A)
% 0.44/0.63           | ~ (v5_orders_2 @ sk_A)
% 0.44/0.63           | ~ (v1_yellow_0 @ sk_A)
% 0.44/0.63           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)
% 0.44/0.63           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['44', '58'])).
% 0.44/0.63  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('61', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('62', plain, ((v1_yellow_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('63', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          ((v2_struct_0 @ sk_A)
% 0.44/0.63           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)
% 0.44/0.63           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.44/0.63  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('65', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.44/0.63           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('clc', [status(thm)], ['63', '64'])).
% 0.44/0.63  thf('66', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (~ (l1_orders_2 @ sk_A)
% 0.44/0.63           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['28', '65'])).
% 0.44/0.63  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('68', plain,
% 0.44/0.63      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.44/0.63  thf('69', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.44/0.63  thf('70', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.44/0.63  thf('71', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.63          | ~ (r2_hidden @ X0 @ sk_B)
% 0.44/0.63          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.63          | (r2_hidden @ X1 @ sk_B)
% 0.44/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.44/0.63  thf('72', plain,
% 0.44/0.63      ((![X0 : $i, X1 : $i]:
% 0.44/0.63          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.44/0.63           | (r2_hidden @ X1 @ sk_B)
% 0.44/0.63           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.44/0.63           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['70', '71'])).
% 0.44/0.63  thf('73', plain,
% 0.44/0.63      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.44/0.63  thf('74', plain,
% 0.44/0.63      ((![X0 : $i, X1 : $i]:
% 0.44/0.63          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.44/0.63           | (r2_hidden @ X1 @ sk_B)
% 0.44/0.63           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['72', '73'])).
% 0.44/0.63  thf('75', plain,
% 0.44/0.63      (((((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63         | (r2_hidden @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.44/0.63         | ~ (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.63              (u1_struct_0 @ sk_A))))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['27', '74'])).
% 0.44/0.63  thf('76', plain,
% 0.44/0.63      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.63           (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.63  thf('77', plain,
% 0.44/0.63      ((((r2_hidden @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.44/0.63         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('clc', [status(thm)], ['75', '76'])).
% 0.44/0.63  thf('78', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.44/0.63          | ((X1) = (X0))
% 0.44/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.44/0.63  thf('79', plain,
% 0.44/0.63      (((((u1_struct_0 @ sk_A) = (sk_B))
% 0.44/0.63         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['77', '78'])).
% 0.44/0.63  thf('80', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('81', plain,
% 0.44/0.63      (((((u1_struct_0 @ sk_A) = (sk_B)) | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['79', '80'])).
% 0.44/0.63  thf('82', plain,
% 0.44/0.63      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['81'])).
% 0.44/0.63  thf('83', plain,
% 0.44/0.63      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.44/0.63        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('84', plain,
% 0.44/0.63      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('split', [status(esa)], ['83'])).
% 0.44/0.63  thf('85', plain,
% 0.44/0.63      (((v1_subset_1 @ sk_B @ sk_B))
% 0.44/0.63         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.44/0.63             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['82', '84'])).
% 0.44/0.63  thf('86', plain,
% 0.44/0.63      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['81'])).
% 0.44/0.63  thf('87', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('88', plain,
% 0.44/0.63      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B)))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['86', '87'])).
% 0.44/0.63  thf(d7_subset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.63       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.44/0.63  thf('89', plain,
% 0.44/0.63      (![X21 : $i, X22 : $i]:
% 0.44/0.63         (~ (v1_subset_1 @ X22 @ X21)
% 0.44/0.63          | ((X22) != (X21))
% 0.44/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.44/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.44/0.63  thf('90', plain,
% 0.44/0.63      (![X21 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))
% 0.44/0.63          | ~ (v1_subset_1 @ X21 @ X21))),
% 0.44/0.63      inference('simplify', [status(thm)], ['89'])).
% 0.44/0.63  thf('91', plain,
% 0.44/0.63      ((~ (v1_subset_1 @ sk_B @ sk_B))
% 0.44/0.63         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['88', '90'])).
% 0.44/0.63  thf('92', plain,
% 0.44/0.63      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.44/0.63       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['85', '91'])).
% 0.44/0.63  thf('93', plain,
% 0.44/0.63      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.44/0.63       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['83'])).
% 0.44/0.63  thf('94', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('95', plain,
% 0.44/0.63      (![X21 : $i, X22 : $i]:
% 0.44/0.63         (((X22) = (X21))
% 0.44/0.63          | (v1_subset_1 @ X22 @ X21)
% 0.44/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.44/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.44/0.63  thf('96', plain,
% 0.44/0.63      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.44/0.63        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.63  thf('97', plain,
% 0.44/0.63      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.44/0.63         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf('98', plain,
% 0.44/0.63      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.44/0.63         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['96', '97'])).
% 0.44/0.63  thf('99', plain,
% 0.44/0.63      (![X7 : $i]:
% 0.44/0.63         (((k3_yellow_0 @ X7) = (k1_yellow_0 @ X7 @ k1_xboole_0))
% 0.44/0.63          | ~ (l1_orders_2 @ X7))),
% 0.44/0.63      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.44/0.63  thf('100', plain,
% 0.44/0.63      (![X12 : $i, X13 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X12)
% 0.44/0.63          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.44/0.63  thf('101', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         ((m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['99', '100'])).
% 0.44/0.63  thf('102', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X0)
% 0.44/0.63          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['101'])).
% 0.44/0.63  thf(t2_subset, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ A @ B ) =>
% 0.44/0.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.44/0.63  thf('103', plain,
% 0.44/0.63      (![X2 : $i, X3 : $i]:
% 0.44/0.63         ((r2_hidden @ X2 @ X3)
% 0.44/0.63          | (v1_xboole_0 @ X3)
% 0.44/0.63          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.44/0.63      inference('cnf', [status(esa)], [t2_subset])).
% 0.44/0.63  thf('104', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (l1_orders_2 @ X0)
% 0.44/0.63          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.44/0.63          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['102', '103'])).
% 0.44/0.63  thf('105', plain,
% 0.44/0.63      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.44/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.63         | ~ (l1_orders_2 @ sk_A)))
% 0.44/0.63         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('sup+', [status(thm)], ['98', '104'])).
% 0.44/0.63  thf('106', plain,
% 0.44/0.63      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.44/0.63         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['96', '97'])).
% 0.44/0.63  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('108', plain,
% 0.44/0.63      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.44/0.63         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.44/0.63  thf('109', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('110', plain,
% 0.44/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.44/0.63         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('clc', [status(thm)], ['108', '109'])).
% 0.44/0.63  thf('111', plain,
% 0.44/0.63      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.44/0.63         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.44/0.63      inference('split', [status(esa)], ['83'])).
% 0.44/0.63  thf('112', plain,
% 0.44/0.63      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.44/0.63       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['110', '111'])).
% 0.44/0.63  thf('113', plain, ($false),
% 0.44/0.63      inference('sat_resolution*', [status(thm)], ['1', '92', '93', '112'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
