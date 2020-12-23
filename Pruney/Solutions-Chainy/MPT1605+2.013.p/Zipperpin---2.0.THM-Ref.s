%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8XBYhbSLTl

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:11 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 221 expanded)
%              Number of leaves         :   36 (  87 expanded)
%              Depth                    :   28
%              Number of atoms          : 1185 (1893 expanded)
%              Number of equality atoms :   24 (  79 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
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
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X19 @ X18 ) @ X19 )
      | ( r1_lattice3 @ X18 @ X19 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
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
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('13',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( sk_D @ X17 @ X19 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_lattice3 @ X18 @ X19 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('17',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
      | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) ) )
      | ~ ( r1_tarski @ X35 @ X37 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X36 ) @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) ) )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('22',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('23',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('24',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ~ ( r1_tarski @ X35 @ X37 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X36 ) @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
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

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r3_orders_2 @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X29: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('36',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_orders_2 @ X18 @ X17 @ ( sk_D @ X17 @ X19 @ X18 ) )
      | ( r1_lattice3 @ X18 @ X19 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('50',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d4_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_yellow_0 @ A )
      <=> ? [B: $i] :
            ( ( r1_lattice3 @ A @ ( u1_struct_0 @ A ) @ B )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_lattice3 @ X21 @ ( u1_struct_0 @ X21 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( v1_yellow_0 @ X21 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ X1 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('56',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ X1 )
      | ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('60',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
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

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( r1_orders_2 @ X25 @ ( k3_yellow_0 @ X25 ) @ X24 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v1_yellow_0 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X31: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('65',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','68'])).

thf('70',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r3_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('74',plain,(
    ! [X29: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('75',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('79',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('80',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','83'])).

thf('85',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X36 ) @ X35 @ X37 )
      | ( r1_tarski @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) ) )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('87',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('88',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('89',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X36 ) @ X35 @ X37 )
      | ( r1_tarski @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('93',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X32: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X32 ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('95',plain,
    ( ( r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['95','96'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('98',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('99',plain,
    ( ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8XBYhbSLTl
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 1376 iterations in 0.698s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.17  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.99/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.17  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.99/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.17  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.99/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.99/1.17  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.99/1.17  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.99/1.17  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.99/1.17  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.99/1.17  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.99/1.17  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.99/1.17  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.99/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.17  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.99/1.17  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.99/1.17  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.99/1.17  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.99/1.17  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.99/1.17  thf(t13_yellow_1, conjecture,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.99/1.17       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.99/1.17         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.17    (~( ![A:$i]:
% 0.99/1.17        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.99/1.17          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.99/1.17            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.99/1.17  thf('0', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t1_subset, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.99/1.17  thf('1', plain,
% 0.99/1.17      (![X12 : $i, X13 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_subset])).
% 0.99/1.17  thf('2', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('3', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf(t1_yellow_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.99/1.17       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.99/1.17  thf('4', plain, (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf(d8_lattice3, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_orders_2 @ A ) =>
% 0.99/1.17       ( ![B:$i,C:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.99/1.17           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.99/1.17             ( ![D:$i]:
% 0.99/1.17               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.99/1.17                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.99/1.17          | (r2_hidden @ (sk_D @ X17 @ X19 @ X18) @ X19)
% 0.99/1.17          | (r1_lattice3 @ X18 @ X19 @ X17)
% 0.99/1.17          | ~ (l1_orders_2 @ X18))),
% 0.99/1.17      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.99/1.17  thf('6', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.99/1.17          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.99/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.17  thf(dt_k2_yellow_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.99/1.17       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.99/1.17  thf('7', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.99/1.17          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.99/1.17      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.99/1.17          | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['3', '8'])).
% 0.99/1.17  thf('10', plain,
% 0.99/1.17      (![X12 : $i, X13 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_subset])).
% 0.99/1.17  thf('11', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.99/1.17          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.99/1.17             X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['9', '10'])).
% 0.99/1.17  thf('12', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('13', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('14', plain,
% 0.99/1.17      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.99/1.17          | (m1_subset_1 @ (sk_D @ X17 @ X19 @ X18) @ (u1_struct_0 @ X18))
% 0.99/1.17          | (r1_lattice3 @ X18 @ X19 @ X17)
% 0.99/1.17          | ~ (l1_orders_2 @ X18))),
% 0.99/1.17      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.99/1.17  thf('15', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.99/1.17          | (m1_subset_1 @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ 
% 0.99/1.17             (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.99/1.17  thf('16', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('18', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.99/1.17          | (m1_subset_1 @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.99/1.17  thf('19', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.99/1.17           sk_A)
% 0.99/1.17          | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['12', '18'])).
% 0.99/1.17  thf('20', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf(t3_yellow_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.99/1.17           ( ![C:$i]:
% 0.99/1.17             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.99/1.17               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.99/1.17                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.99/1.17  thf('21', plain,
% 0.99/1.17      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ (k2_yellow_1 @ X36)))
% 0.99/1.17          | ~ (r1_tarski @ X35 @ X37)
% 0.99/1.17          | (r3_orders_2 @ (k2_yellow_1 @ X36) @ X35 @ X37)
% 0.99/1.17          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ (k2_yellow_1 @ X36)))
% 0.99/1.17          | (v1_xboole_0 @ X36))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.99/1.17  thf('22', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('23', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X35 @ X36)
% 0.99/1.17          | ~ (r1_tarski @ X35 @ X37)
% 0.99/1.17          | (r3_orders_2 @ (k2_yellow_1 @ X36) @ X35 @ X37)
% 0.99/1.17          | ~ (m1_subset_1 @ X37 @ X36)
% 0.99/1.17          | (v1_xboole_0 @ X36))),
% 0.99/1.17      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.99/1.17  thf('25', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v1_xboole_0 @ sk_A)
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.99/1.17          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.99/1.17          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['20', '24'])).
% 0.99/1.17  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.99/1.17  thf('26', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.99/1.17      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.99/1.17  thf('27', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v1_xboole_0 @ sk_A)
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.99/1.17          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['25', '26'])).
% 0.99/1.17  thf('28', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('29', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.99/1.17      inference('clc', [status(thm)], ['27', '28'])).
% 0.99/1.17  thf('30', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.99/1.17          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.99/1.17             (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['19', '29'])).
% 0.99/1.17  thf('31', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf(redefinition_r3_orders_2, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.99/1.17         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.99/1.17         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.99/1.17  thf('32', plain,
% 0.99/1.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.99/1.17          | ~ (l1_orders_2 @ X15)
% 0.99/1.17          | ~ (v3_orders_2 @ X15)
% 0.99/1.17          | (v2_struct_0 @ X15)
% 0.99/1.17          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.99/1.17          | (r1_orders_2 @ X15 @ X14 @ X16)
% 0.99/1.17          | ~ (r3_orders_2 @ X15 @ X14 @ X16))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.99/1.17  thf('33', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.99/1.17          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['31', '32'])).
% 0.99/1.17  thf('34', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf(fc5_yellow_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.99/1.17       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.99/1.17       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.99/1.17       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.99/1.17  thf('35', plain, (![X29 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X29))),
% 0.99/1.17      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.99/1.17  thf('36', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.99/1.17  thf('37', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.99/1.17          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ X0)
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.99/1.17      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.99/1.17  thf('38', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17          | ~ (m1_subset_1 @ 
% 0.99/1.17               (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.99/1.17          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.99/1.17             (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)))
% 0.99/1.17          | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['30', '37'])).
% 0.99/1.17  thf('39', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('40', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17          | ~ (m1_subset_1 @ 
% 0.99/1.17               (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.99/1.17          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.99/1.17             (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A))))),
% 0.99/1.17      inference('demod', [status(thm)], ['38', '39'])).
% 0.99/1.17  thf('41', plain,
% 0.99/1.17      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.99/1.17        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.99/1.17           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.99/1.17        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['11', '40'])).
% 0.99/1.17  thf('42', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.99/1.17           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.99/1.17        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.99/1.17      inference('simplify', [status(thm)], ['41'])).
% 0.99/1.17  thf('43', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('44', plain,
% 0.99/1.17      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.99/1.17          | ~ (r1_orders_2 @ X18 @ X17 @ (sk_D @ X17 @ X19 @ X18))
% 0.99/1.17          | (r1_lattice3 @ X18 @ X19 @ X17)
% 0.99/1.17          | ~ (l1_orders_2 @ X18))),
% 0.99/1.17      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.99/1.17  thf('45', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.99/1.17          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.99/1.17               (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['43', '44'])).
% 0.99/1.17  thf('46', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.99/1.17  thf('47', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.99/1.17          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.99/1.17               (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0))))),
% 0.99/1.17      inference('demod', [status(thm)], ['45', '46'])).
% 0.99/1.17  thf('48', plain,
% 0.99/1.17      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.99/1.17        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.99/1.17        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['42', '47'])).
% 0.99/1.17  thf('49', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('50', plain,
% 0.99/1.17      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.99/1.17        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['48', '49'])).
% 0.99/1.17  thf('51', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.99/1.17      inference('simplify', [status(thm)], ['50'])).
% 0.99/1.17  thf('52', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf(d4_yellow_0, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_orders_2 @ A ) =>
% 0.99/1.17       ( ( v1_yellow_0 @ A ) <=>
% 0.99/1.17         ( ?[B:$i]:
% 0.99/1.17           ( ( r1_lattice3 @ A @ ( u1_struct_0 @ A ) @ B ) & 
% 0.99/1.17             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.99/1.17  thf('53', plain,
% 0.99/1.17      (![X21 : $i, X22 : $i]:
% 0.99/1.17         (~ (r1_lattice3 @ X21 @ (u1_struct_0 @ X21) @ X22)
% 0.99/1.17          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.99/1.17          | (v1_yellow_0 @ X21)
% 0.99/1.17          | ~ (l1_orders_2 @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [d4_yellow_0])).
% 0.99/1.17  thf('54', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ X1)
% 0.99/1.17          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['52', '53'])).
% 0.99/1.17  thf('55', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.99/1.17  thf('56', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('57', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ X1)
% 0.99/1.17          | (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.99/1.17  thf('58', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.99/1.17        | (v1_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['51', '57'])).
% 0.99/1.17  thf('59', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('60', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (v1_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['58', '59'])).
% 0.99/1.17  thf('61', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf(t44_yellow_0, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.99/1.17         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.99/1.17           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.99/1.17  thf('62', plain,
% 0.99/1.17      (![X24 : $i, X25 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.99/1.17          | (r1_orders_2 @ X25 @ (k3_yellow_0 @ X25) @ X24)
% 0.99/1.17          | ~ (l1_orders_2 @ X25)
% 0.99/1.17          | ~ (v1_yellow_0 @ X25)
% 0.99/1.17          | ~ (v5_orders_2 @ X25)
% 0.99/1.17          | (v2_struct_0 @ X25))),
% 0.99/1.17      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.99/1.17  thf('63', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.99/1.17             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X1))),
% 0.99/1.17      inference('sup-', [status(thm)], ['61', '62'])).
% 0.99/1.17  thf('64', plain, (![X31 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X31))),
% 0.99/1.17      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.99/1.17  thf('65', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.99/1.17  thf('66', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.99/1.17             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X1))),
% 0.99/1.17      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.99/1.17  thf('67', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.99/1.17             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['60', '66'])).
% 0.99/1.17  thf('68', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.99/1.17          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.99/1.17             (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.99/1.17      inference('simplify', [status(thm)], ['67'])).
% 0.99/1.17  thf('69', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.99/1.17           (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['2', '68'])).
% 0.99/1.17  thf('70', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('71', plain,
% 0.99/1.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.99/1.17          | ~ (l1_orders_2 @ X15)
% 0.99/1.17          | ~ (v3_orders_2 @ X15)
% 0.99/1.17          | (v2_struct_0 @ X15)
% 0.99/1.17          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.99/1.17          | (r3_orders_2 @ X15 @ X14 @ X16)
% 0.99/1.17          | ~ (r1_orders_2 @ X15 @ X14 @ X16))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.99/1.17  thf('72', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.99/1.17          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.99/1.17          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['70', '71'])).
% 0.99/1.17  thf('73', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('74', plain, (![X29 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X29))),
% 0.99/1.17      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.99/1.17  thf('75', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.99/1.17  thf('76', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X1 @ X0)
% 0.99/1.17          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.99/1.17          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ X0)
% 0.99/1.17          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.99/1.17      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.99/1.17  thf('77', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.99/1.17        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.99/1.17           (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.99/1.17        | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['69', '76'])).
% 0.99/1.17  thf('78', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('79', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf(dt_k3_yellow_0, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_orders_2 @ A ) =>
% 0.99/1.17       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.99/1.17  thf('80', plain,
% 0.99/1.17      (![X23 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (k3_yellow_0 @ X23) @ (u1_struct_0 @ X23))
% 0.99/1.17          | ~ (l1_orders_2 @ X23))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.99/1.17  thf('81', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.99/1.17          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['79', '80'])).
% 0.99/1.17  thf('82', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.99/1.17  thf('83', plain,
% 0.99/1.17      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.99/1.17      inference('demod', [status(thm)], ['81', '82'])).
% 0.99/1.17  thf('84', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.99/1.17           (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['77', '78', '83'])).
% 0.99/1.17  thf('85', plain,
% 0.99/1.17      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.99/1.17         (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.99/1.17        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.99/1.17      inference('simplify', [status(thm)], ['84'])).
% 0.99/1.17  thf('86', plain,
% 0.99/1.17      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ (k2_yellow_1 @ X36)))
% 0.99/1.17          | ~ (r3_orders_2 @ (k2_yellow_1 @ X36) @ X35 @ X37)
% 0.99/1.17          | (r1_tarski @ X35 @ X37)
% 0.99/1.17          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ (k2_yellow_1 @ X36)))
% 0.99/1.17          | (v1_xboole_0 @ X36))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.99/1.17  thf('87', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('88', plain,
% 0.99/1.17      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.99/1.17  thf('89', plain,
% 0.99/1.17      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X35 @ X36)
% 0.99/1.17          | ~ (r3_orders_2 @ (k2_yellow_1 @ X36) @ X35 @ X37)
% 0.99/1.17          | (r1_tarski @ X35 @ X37)
% 0.99/1.17          | ~ (m1_subset_1 @ X37 @ X36)
% 0.99/1.17          | (v1_xboole_0 @ X36))),
% 0.99/1.17      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.99/1.17  thf('90', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (v1_xboole_0 @ sk_A)
% 0.99/1.17        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.99/1.17        | (r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.99/1.17        | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['85', '89'])).
% 0.99/1.17  thf('91', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('92', plain,
% 0.99/1.17      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.99/1.17      inference('demod', [status(thm)], ['81', '82'])).
% 0.99/1.17  thf('93', plain,
% 0.99/1.17      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.99/1.17        | (v1_xboole_0 @ sk_A)
% 0.99/1.17        | (r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.99/1.17  thf(fc6_yellow_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.99/1.17       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.99/1.17         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.99/1.17  thf('94', plain,
% 0.99/1.17      (![X32 : $i]:
% 0.99/1.17         (~ (v2_struct_0 @ (k2_yellow_1 @ X32)) | (v1_xboole_0 @ X32))),
% 0.99/1.17      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.99/1.17  thf('95', plain,
% 0.99/1.17      (((r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)
% 0.99/1.17        | (v1_xboole_0 @ sk_A))),
% 0.99/1.17      inference('clc', [status(thm)], ['93', '94'])).
% 0.99/1.17  thf('96', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('97', plain,
% 0.99/1.17      ((r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ sk_A)) @ k1_xboole_0)),
% 0.99/1.17      inference('clc', [status(thm)], ['95', '96'])).
% 0.99/1.17  thf(t3_xboole_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.99/1.17  thf('98', plain,
% 0.99/1.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.99/1.17  thf('99', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) = (k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['97', '98'])).
% 0.99/1.17  thf('100', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('101', plain, ($false),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 0.99/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
