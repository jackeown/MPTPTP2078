%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JvBnjI59XO

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 254 expanded)
%              Number of leaves         :   36 (  98 expanded)
%              Depth                    :   22
%              Number of atoms          : 1114 (2182 expanded)
%              Number of equality atoms :   23 (  92 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('1',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('3',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X11 @ X10 ) @ X11 )
      | ( r1_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('14',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('16',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('17',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r3_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X21: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('30',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('34',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_orders_2 @ X10 @ X9 @ ( sk_D @ X9 @ X11 @ X10 ) )
      | ( r1_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('44',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_lattice3 @ X13 @ ( u1_struct_0 @ X13 ) @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( v1_yellow_0 @ X13 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ X1 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ X1 )
      | ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('54',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ ( k3_yellow_0 @ X17 ) @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v1_yellow_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('59',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','62'])).

thf('64',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('65',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('70',plain,(
    r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('72',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('74',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('75',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t25_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('77',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_orders_2 @ X7 @ X6 @ X8 )
      | ~ ( r1_orders_2 @ X7 @ X8 @ X6 )
      | ( X6 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( X1 = X2 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('80',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('81',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( X1 = X2 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('85',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('86',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['63','88'])).

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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JvBnjI59XO
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 103 iterations in 0.099s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.56  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.56  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.21/0.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.56  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.56  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.56  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.56  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.56  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(t13_yellow_1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.56         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.56            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.21/0.56  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t1_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.56  thf('3', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(t1_yellow_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.56       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.56  thf('5', plain, (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf(d8_lattice3, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_orders_2 @ A ) =>
% 0.21/0.56       ( ![B:$i,C:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.21/0.56             ( ![D:$i]:
% 0.21/0.56               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.56          | (r2_hidden @ (sk_D @ X9 @ X11 @ X10) @ X11)
% 0.21/0.56          | (r1_lattice3 @ X10 @ X11 @ X9)
% 0.21/0.56          | ~ (l1_orders_2 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.56          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf(dt_k2_yellow_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.56       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.56  thf('8', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.56          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.21/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.21/0.56          | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.21/0.56             X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.21/0.56             X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.56  thf('14', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(t3_yellow_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.56               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.21/0.56                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.21/0.56          | ~ (r1_tarski @ X27 @ X29)
% 0.21/0.56          | (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.21/0.56          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.21/0.56          | (v1_xboole_0 @ X28))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X27 @ X28)
% 0.21/0.56          | ~ (r1_tarski @ X27 @ X29)
% 0.21/0.56          | (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.21/0.56          | ~ (m1_subset_1 @ X29 @ X28)
% 0.21/0.56          | (v1_xboole_0 @ X28))),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.56          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.21/0.56          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.56  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.56          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.21/0.56        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.56           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.56          | ~ (l1_orders_2 @ X4)
% 0.21/0.56          | ~ (v3_orders_2 @ X4)
% 0.21/0.56          | (v2_struct_0 @ X4)
% 0.21/0.56          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.56          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.21/0.56          | ~ (r3_orders_2 @ X4 @ X3 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.56          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.56          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf(fc5_yellow_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.56       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.56       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.56       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.56  thf('29', plain, (![X21 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.56  thf('30', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.56          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.21/0.56        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | ~ (m1_subset_1 @ 
% 0.21/0.56             (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.21/0.56        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.56           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.21/0.56        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '31'])).
% 0.21/0.56  thf('33', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.21/0.56        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | ~ (m1_subset_1 @ 
% 0.21/0.56             (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.21/0.56        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.56           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.21/0.56        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.56           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.21/0.56        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.56           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.21/0.56        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.56          | ~ (r1_orders_2 @ X10 @ X9 @ (sk_D @ X9 @ X11 @ X10))
% 0.21/0.56          | (r1_lattice3 @ X10 @ X11 @ X9)
% 0.21/0.56          | ~ (l1_orders_2 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.56          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.21/0.56               (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.56  thf('40', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.56          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.21/0.56               (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.21/0.56        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.21/0.56        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '41'])).
% 0.21/0.56  thf('43', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.21/0.56        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf(d4_yellow_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_orders_2 @ A ) =>
% 0.21/0.56       ( ( v1_yellow_0 @ A ) <=>
% 0.21/0.56         ( ?[B:$i]:
% 0.21/0.56           ( ( r1_lattice3 @ A @ ( u1_struct_0 @ A ) @ B ) & 
% 0.21/0.56             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i]:
% 0.21/0.56         (~ (r1_lattice3 @ X13 @ (u1_struct_0 @ X13) @ X14)
% 0.21/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.56          | (v1_yellow_0 @ X13)
% 0.21/0.56          | ~ (l1_orders_2 @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_yellow_0])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ X1)
% 0.21/0.56          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ X1)
% 0.21/0.56          | (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.56        | (v1_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['45', '51'])).
% 0.21/0.56  thf('53', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | (v1_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf(t44_yellow_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.21/0.56         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.56          | (r1_orders_2 @ X17 @ (k3_yellow_0 @ X17) @ X16)
% 0.21/0.56          | ~ (l1_orders_2 @ X17)
% 0.21/0.56          | ~ (v1_yellow_0 @ X17)
% 0.21/0.56          | ~ (v5_orders_2 @ X17)
% 0.21/0.56          | (v2_struct_0 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.21/0.56             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.56  thf('58', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.56  thf('59', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.21/0.56             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X1))),
% 0.21/0.56      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.21/0.56             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.21/0.56          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['54', '60'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.56          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.21/0.56             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.21/0.56          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['61'])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.21/0.56           (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '62'])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf(dt_k3_yellow_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_orders_2 @ A ) =>
% 0.21/0.56       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X15 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k3_yellow_0 @ X15) @ (u1_struct_0 @ X15))
% 0.21/0.56          | ~ (l1_orders_2 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.21/0.56          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.56  thf('67', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.21/0.56      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.56        (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.56          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.56  thf('72', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.21/0.56        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.56           (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.56        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.21/0.56      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.56  thf('74', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('75', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.56           (k3_yellow_0 @ (k2_yellow_1 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf(t25_orders_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.21/0.56                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.21/0.56          | ~ (r1_orders_2 @ X7 @ X6 @ X8)
% 0.21/0.56          | ~ (r1_orders_2 @ X7 @ X8 @ X6)
% 0.21/0.56          | ((X6) = (X8))
% 0.21/0.56          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.56          | ~ (l1_orders_2 @ X7)
% 0.21/0.56          | ~ (v5_orders_2 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [t25_orders_2])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.56          | ((X1) = (X2))
% 0.21/0.56          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.56          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.56  thf('79', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.56  thf('80', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      (![X25 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X25)) = (X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.56          | ((X1) = (X2))
% 0.21/0.56          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.56          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 0.21/0.56      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | ~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.21/0.56             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.21/0.56        | ((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) = (k1_xboole_0))
% 0.21/0.56        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.56        | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['75', '82'])).
% 0.21/0.56  thf('84', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.21/0.56      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | ~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.21/0.56             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.21/0.56        | ((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.21/0.56  thf('87', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('88', plain,
% 0.21/0.56      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.56        | ~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.21/0.56             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.21/0.56  thf('89', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['63', '88'])).
% 0.21/0.56  thf(fc6_yellow_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.21/0.56         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.21/0.56  thf('90', plain,
% 0.21/0.56      (![X24 : $i]:
% 0.21/0.56         (~ (v2_struct_0 @ (k2_yellow_1 @ X24)) | (v1_xboole_0 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.21/0.56  thf('91', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.56  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
