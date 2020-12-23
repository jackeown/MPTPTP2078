%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EpFMfAQfFt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 624 expanded)
%              Number of leaves         :   38 ( 223 expanded)
%              Depth                    :   32
%              Number of atoms          : 1242 (5846 expanded)
%              Number of equality atoms :   42 ( 254 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t13_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( r2_hidden @ k1_xboole_0 @ A )
         => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_yellow_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( ( k3_yellow_0 @ X6 )
        = ( k1_yellow_0 @ X6 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('2',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r2_lattice3 @ X17 @ k1_xboole_0 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('12',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t15_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ C @ D ) ) )
              & ( r2_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X11 @ X12 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_lattice3 @ X13 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X13 ) )
      | ( r1_yellow_0 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X2 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( m1_subset_1 @ ( sk_D_1 @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('16',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('17',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X2 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( m1_subset_1 @ ( sk_D_1 @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('23',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('25',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('26',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r3_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('38',plain,(
    ! [X21: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('39',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,
    ( ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_orders_2 @ X13 @ X11 @ ( sk_D_1 @ X11 @ X12 @ X13 ) )
      | ~ ( r2_lattice3 @ X13 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X13 ) )
      | ( r1_yellow_0 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('47',plain,
    ( ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('49',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('50',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('51',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('53',plain,
    ( ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

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

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_lattice3 @ X7 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X8 @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ( X9
        = ( k1_yellow_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_yellow_0 @ X7 @ X8 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X2 )
      | ( X1
        = ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X2 ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('59',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X2 )
      | ( X1
        = ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X2 ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
      | ( X0
        = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','61'])).

thf('63',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('67',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('69',plain,
    ( ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('71',plain,
    ( ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_lattice3 @ X7 @ X8 @ X9 )
      | ~ ( r1_orders_2 @ X7 @ X9 @ ( sk_D @ X9 @ X8 @ X7 ) )
      | ( X9
        = ( k1_yellow_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_yellow_0 @ X7 @ X8 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('78',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('79',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('80',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('81',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ~ ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('84',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','84'])).

thf('86',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('87',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('90',plain,(
    ! [X24: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X24 ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('91',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EpFMfAQfFt
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 104 iterations in 0.066s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.54  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.20/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.54  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.20/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.54  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.20/0.54  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.20/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.54  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.20/0.54  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.20/0.54  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.54  thf(t13_yellow_1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.54         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.54            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.20/0.54  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d11_yellow_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_orders_2 @ A ) =>
% 0.20/0.54       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X6 : $i]:
% 0.20/0.54         (((k3_yellow_0 @ X6) = (k1_yellow_0 @ X6 @ k1_xboole_0))
% 0.20/0.54          | ~ (l1_orders_2 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.20/0.54  thf('2', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t1_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.54  thf('4', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(t1_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.54       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.54  thf('5', plain, (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf(t6_yellow_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_orders_2 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.20/0.54             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.20/0.54          | (r2_lattice3 @ X17 @ k1_xboole_0 @ X16)
% 0.20/0.54          | ~ (l1_orders_2 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf(dt_k2_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.54       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.54  thf('8', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf(t15_yellow_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( r1_yellow_0 @ A @ B ) <=>
% 0.20/0.54           ( ?[C:$i]:
% 0.20/0.54             ( ( ![D:$i]:
% 0.20/0.54                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                   ( ( r2_lattice3 @ A @ B @ D ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) & 
% 0.20/0.54               ( r2_lattice3 @ A @ B @ C ) & 
% 0.20/0.54               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         ((m1_subset_1 @ (sk_D_1 @ X11 @ X12 @ X13) @ (u1_struct_0 @ X13))
% 0.20/0.54          | ~ (r2_lattice3 @ X13 @ X12 @ X11)
% 0.20/0.54          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X13))
% 0.20/0.54          | (r1_yellow_0 @ X13 @ X12)
% 0.20/0.54          | ~ (l1_orders_2 @ X13)
% 0.20/0.54          | ~ (v5_orders_2 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | (r1_yellow_0 @ (k2_yellow_1 @ X0) @ X2)
% 0.20/0.54          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.20/0.54          | (m1_subset_1 @ (sk_D_1 @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ 
% 0.20/0.54             (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf(fc5_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.54       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.54       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.54       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.54  thf('15', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.54  thf('16', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | (r1_yellow_0 @ (k2_yellow_1 @ X0) @ X2)
% 0.20/0.54          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.20/0.54          | (m1_subset_1 @ (sk_D_1 @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (((m1_subset_1 @ 
% 0.20/0.54         (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '18'])).
% 0.20/0.54  thf('20', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (((m1_subset_1 @ 
% 0.20/0.54         (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((m1_subset_1 @ 
% 0.20/0.54         (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('23', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(t3_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.54               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.20/0.54                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.20/0.54          | ~ (r1_tarski @ X27 @ X29)
% 0.20/0.54          | (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.20/0.54          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.20/0.54          | (v1_xboole_0 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X27 @ X28)
% 0.20/0.54          | ~ (r1_tarski @ X27 @ X29)
% 0.20/0.54          | (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.20/0.54          | ~ (m1_subset_1 @ X29 @ X28)
% 0.20/0.54          | (v1_xboole_0 @ X28))),
% 0.20/0.54      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.54          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.20/0.54          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '27'])).
% 0.20/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.54  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.54          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('31', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (((r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['22', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf(redefinition_r3_orders_2, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.54         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.54         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.20/0.54          | ~ (l1_orders_2 @ X4)
% 0.20/0.54          | ~ (v3_orders_2 @ X4)
% 0.20/0.54          | (v2_struct_0 @ X4)
% 0.20/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.54          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.20/0.54          | ~ (r3_orders_2 @ X4 @ X3 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.20/0.54          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('38', plain, (![X21 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.54  thf('39', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ X0)
% 0.20/0.54          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['33', '40'])).
% 0.20/0.54  thf('42', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (((r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['21', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         (~ (r1_orders_2 @ X13 @ X11 @ (sk_D_1 @ X11 @ X12 @ X13))
% 0.20/0.54          | ~ (r2_lattice3 @ X13 @ X12 @ X11)
% 0.20/0.54          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X13))
% 0.20/0.54          | (r1_yellow_0 @ X13 @ X12)
% 0.20/0.54          | ~ (l1_orders_2 @ X13)
% 0.20/0.54          | ~ (v5_orders_2 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (((r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | ~ (m1_subset_1 @ k1_xboole_0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf('48', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.54  thf('49', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('51', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (((r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['47', '48', '49', '50', '51', '52'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf(d9_yellow_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_orders_2 @ A ) =>
% 0.20/0.54       ( ![B:$i,C:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ( r1_yellow_0 @ A @ B ) =>
% 0.20/0.54             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.20/0.54               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.20/0.54                 ( ![D:$i]:
% 0.20/0.54                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.20/0.54                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (r2_lattice3 @ X7 @ X8 @ X9)
% 0.20/0.54          | (m1_subset_1 @ (sk_D @ X9 @ X8 @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.54          | ((X9) = (k1_yellow_0 @ X7 @ X8))
% 0.20/0.54          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.54          | ~ (r1_yellow_0 @ X7 @ X8)
% 0.20/0.54          | ~ (l1_orders_2 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (r1_yellow_0 @ (k2_yellow_1 @ X0) @ X2)
% 0.20/0.54          | ((X1) = (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X2))
% 0.20/0.54          | (m1_subset_1 @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ 
% 0.20/0.54             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.20/0.54          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.54  thf('58', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (r1_yellow_0 @ (k2_yellow_1 @ X0) @ X2)
% 0.20/0.54          | ((X1) = (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X2))
% 0.20/0.54          | (m1_subset_1 @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X0)
% 0.20/0.54          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54          | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.20/0.54          | (m1_subset_1 @ (sk_D @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54             sk_A)
% 0.20/0.54          | ((X0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['54', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '61'])).
% 0.20/0.54  thf('63', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      ((((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ X0)
% 0.20/0.54          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      ((((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.54  thf('70', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      ((((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54         (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['64', '72'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54         (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (r2_lattice3 @ X7 @ X8 @ X9)
% 0.20/0.54          | ~ (r1_orders_2 @ X7 @ X9 @ (sk_D @ X9 @ X8 @ X7))
% 0.20/0.54          | ((X9) = (k1_yellow_0 @ X7 @ X8))
% 0.20/0.54          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.54          | ~ (r1_yellow_0 @ X7 @ X8)
% 0.20/0.54          | ~ (l1_orders_2 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | ~ (m1_subset_1 @ k1_xboole_0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.54  thf('77', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('79', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | ~ (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      ((~ (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.54  thf('84', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.20/0.54      inference('clc', [status(thm)], ['82', '83'])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '84'])).
% 0.20/0.54  thf('86', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('87', plain,
% 0.20/0.54      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.54  thf('88', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('89', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.20/0.54  thf(fc6_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.20/0.54         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      (![X24 : $i]:
% 0.20/0.54         (~ (v2_struct_0 @ (k2_yellow_1 @ X24)) | (v1_xboole_0 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.20/0.54  thf('91', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
