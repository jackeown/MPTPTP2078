%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aBYyP87wiv

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 235 expanded)
%              Number of leaves         :   38 (  92 expanded)
%              Depth                    :   28
%              Number of atoms          : 1153 (1982 expanded)
%              Number of equality atoms :   24 (  80 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('2',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('13',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('15',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('16',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r3_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X21: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('29',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('33',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X7 @ ( sk_D @ X7 @ X9 @ X8 ) )
      | ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('43',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d4_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_yellow_0 @ A )
      <=> ? [B: $i] :
            ( ( r1_lattice3 @ A @ ( u1_struct_0 @ A ) @ B )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_lattice3 @ X12 @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( v1_yellow_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ X1 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('49',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ X1 )
      | ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('53',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ ( k3_yellow_0 @ X17 ) @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v1_yellow_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('58',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','61'])).

thf('63',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('64',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r3_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r1_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('67',plain,(
    ! [X21: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('68',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X11: $i] :
      ( ( ( k3_yellow_0 @ X11 )
        = ( k1_yellow_0 @ X11 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('73',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','80'])).

thf('82',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ( r1_tarski @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('84',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('85',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('86',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ( r1_tarski @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('89',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('90',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('91',plain,(
    ! [X24: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X24 ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('92',plain,
    ( ( r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['92','93'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('95',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('96',plain,
    ( ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aBYyP87wiv
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 104 iterations in 0.074s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.20/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.52  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.20/0.52  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.52  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.52  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.20/0.52  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.20/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.52  thf(t13_yellow_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.52         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.52            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.20/0.52  thf('0', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t1_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]: ((m1_subset_1 @ X2 @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.52  thf('2', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('3', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(t1_yellow_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.52       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.52  thf('4', plain, (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf(d8_lattice3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_orders_2 @ A ) =>
% 0.20/0.52       ( ![B:$i,C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.20/0.52             ( ![D:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.20/0.52          | (r1_lattice3 @ X8 @ X9 @ X7)
% 0.20/0.52          | ~ (l1_orders_2 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(dt_k2_yellow_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.52       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.52  thf('7', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.20/0.52          | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]: ((m1_subset_1 @ X2 @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.20/0.52          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.52             X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.20/0.52          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.52             X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('13', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(t3_yellow_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.52               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.20/0.52                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.20/0.52          | ~ (r1_tarski @ X27 @ X29)
% 0.20/0.52          | (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.20/0.52          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.20/0.52          | (v1_xboole_0 @ X28))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X27 @ X28)
% 0.20/0.52          | ~ (r1_tarski @ X27 @ X29)
% 0.20/0.52          | (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.20/0.52          | ~ (m1_subset_1 @ X29 @ X28)
% 0.20/0.52          | (v1_xboole_0 @ X28))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.52          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.20/0.52          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '17'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.52          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.20/0.52        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.52           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf(redefinition_r3_orders_2, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.52          | ~ (l1_orders_2 @ X5)
% 0.20/0.52          | ~ (v3_orders_2 @ X5)
% 0.20/0.52          | (v2_struct_0 @ X5)
% 0.20/0.52          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.52          | (r1_orders_2 @ X5 @ X4 @ X6)
% 0.20/0.52          | ~ (r3_orders_2 @ X5 @ X4 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.52          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.20/0.52          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf(fc5_yellow_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.52       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.52       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.52       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.52  thf('28', plain, (![X21 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.52  thf('29', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.52          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ X0)
% 0.20/0.52          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.20/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | ~ (m1_subset_1 @ 
% 0.20/0.52             (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.52        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.52           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.20/0.52        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '30'])).
% 0.20/0.52  thf('32', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.20/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | ~ (m1_subset_1 @ 
% 0.20/0.52             (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.20/0.52        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.52           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.20/0.52        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.52           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.20/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.52           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.20/0.52        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.20/0.52          | ~ (r1_orders_2 @ X8 @ X7 @ (sk_D @ X7 @ X9 @ X8))
% 0.20/0.52          | (r1_lattice3 @ X8 @ X9 @ X7)
% 0.20/0.52          | ~ (l1_orders_2 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.20/0.52          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.20/0.52               (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.20/0.52          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.20/0.52               (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.20/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.20/0.52        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '40'])).
% 0.20/0.52  thf('42', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.20/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf(d4_yellow_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_orders_2 @ A ) =>
% 0.20/0.52       ( ( v1_yellow_0 @ A ) <=>
% 0.20/0.52         ( ?[B:$i]:
% 0.20/0.52           ( ( r1_lattice3 @ A @ ( u1_struct_0 @ A ) @ B ) & 
% 0.20/0.52             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r1_lattice3 @ X12 @ (u1_struct_0 @ X12) @ X13)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.52          | (v1_yellow_0 @ X12)
% 0.20/0.52          | ~ (l1_orders_2 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_yellow_0])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ X1)
% 0.20/0.52          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ X1)
% 0.20/0.52          | (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.52        | (v1_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '50'])).
% 0.20/0.52  thf('52', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (v1_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf(t44_yellow_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.20/0.52         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.20/0.52          | (r1_orders_2 @ X17 @ (k3_yellow_0 @ X17) @ X16)
% 0.20/0.52          | ~ (l1_orders_2 @ X17)
% 0.20/0.52          | ~ (v1_yellow_0 @ X17)
% 0.20/0.52          | ~ (v5_orders_2 @ X17)
% 0.20/0.52          | (v2_struct_0 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.20/0.52             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.52  thf('58', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.20/0.52             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.52             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.20/0.52          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.52          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.52             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.20/0.52          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.52           (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.52          | ~ (l1_orders_2 @ X5)
% 0.20/0.52          | ~ (v3_orders_2 @ X5)
% 0.20/0.52          | (v2_struct_0 @ X5)
% 0.20/0.52          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.52          | (r3_orders_2 @ X5 @ X4 @ X6)
% 0.20/0.52          | ~ (r1_orders_2 @ X5 @ X4 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.52          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.20/0.52          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('67', plain, (![X21 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.52  thf('68', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.52          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.52          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ X0)
% 0.20/0.52          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.52        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.52           (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.20/0.52        | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['62', '69'])).
% 0.20/0.52  thf('71', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(d11_yellow_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_orders_2 @ A ) =>
% 0.20/0.52       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (((k3_yellow_0 @ X11) = (k1_yellow_0 @ X11 @ k1_xboole_0))
% 0.20/0.52          | ~ (l1_orders_2 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf(dt_k1_yellow_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( l1_orders_2 @ A ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ X14)
% 0.20/0.52          | (m1_subset_1 @ (k1_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X1) @ X0)
% 0.20/0.52          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['73', '74'])).
% 0.20/0.52  thf('76', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X1) @ X0)),
% 0.20/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.20/0.52          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['72', '77'])).
% 0.20/0.52  thf('79', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.20/0.52      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.52           (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['70', '71', '80'])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.52         (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.20/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.52  thf('83', plain,
% 0.20/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.20/0.52          | ~ (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.20/0.52          | (r1_tarski @ X27 @ X29)
% 0.20/0.52          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.20/0.52          | (v1_xboole_0 @ X28))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X27 @ X28)
% 0.20/0.52          | ~ (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.20/0.52          | (r1_tarski @ X27 @ X29)
% 0.20/0.52          | ~ (m1_subset_1 @ X29 @ X28)
% 0.20/0.52          | (v1_xboole_0 @ X28))),
% 0.20/0.52      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (v1_xboole_0 @ sk_A)
% 0.20/0.52        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.52        | (r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.20/0.52        | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['82', '86'])).
% 0.20/0.52  thf('88', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.20/0.52      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.52        | (v1_xboole_0 @ sk_A)
% 0.20/0.52        | (r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.20/0.52  thf(fc6_yellow_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.20/0.52         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.20/0.52  thf('91', plain,
% 0.20/0.52      (![X24 : $i]:
% 0.20/0.52         (~ (v2_struct_0 @ (k2_yellow_1 @ X24)) | (v1_xboole_0 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      (((r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.20/0.52        | (v1_xboole_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.52  thf('93', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      ((r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)),
% 0.20/0.52      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.52  thf(t3_xboole_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.52  thf('96', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.52  thf('97', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('98', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
