%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TE8uN20z9J

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:12 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 413 expanded)
%              Number of leaves         :   38 ( 140 expanded)
%              Depth                    :   26
%              Number of atoms          : 1531 (4058 expanded)
%              Number of equality atoms :   62 ( 176 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_yellow_0_type,type,(
    v2_yellow_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t15_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v2_yellow_0 @ ( k2_yellow_1 @ A ) )
       => ( r2_hidden @ ( k3_tarski @ A ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( v2_yellow_0 @ ( k2_yellow_1 @ A ) )
         => ( r2_hidden @ ( k3_tarski @ A ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ ( sk_D @ X9 @ X5 ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('2',plain,(
    v2_yellow_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d5_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_yellow_0 @ A )
      <=> ? [B: $i] :
            ( ( r2_lattice3 @ A @ ( u1_struct_0 @ A ) @ B )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X22: $i] :
      ( ~ ( v2_yellow_0 @ X22 )
      | ( m1_subset_1 @ ( sk_B @ X22 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('14',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('15',plain,(
    ! [X5: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X10 )
      | ~ ( r2_hidden @ X10 @ X5 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('22',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('25',plain,(
    v2_yellow_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('27',plain,(
    ! [X22: $i] :
      ( ~ ( v2_yellow_0 @ X22 )
      | ( r2_lattice3 @ X22 @ ( u1_struct_0 @ X22 ) @ ( sk_B @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

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

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_lattice3 @ X19 @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_orders_2 @ X19 @ X21 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('36',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X3 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['2','7'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('44',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
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

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( r3_orders_2 @ X16 @ X15 @ X17 )
      | ~ ( r1_orders_2 @ X16 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X27: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('49',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['2','7'])).

thf('53',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('56',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ ( k2_yellow_1 @ X34 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X34 ) @ X33 @ X35 )
      | ( r1_tarski @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ ( k2_yellow_1 @ X34 ) ) )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('57',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('58',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('59',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X34 ) @ X33 @ X35 )
      | ( r1_tarski @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_tarski @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['2','7'])).

thf('62',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r1_tarski @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
        = ( k3_tarski @ sk_A ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('70',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ ( sk_D @ X9 @ X5 ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('72',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    r2_hidden @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) @ ( k3_tarski @ sk_A ) )
      | ( r1_tarski @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('82',plain,
    ( ( r1_tarski @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( r1_tarski @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['75','85'])).

thf('87',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('88',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X5: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X10 )
      | ~ ( r2_hidden @ X10 @ X5 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('91',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['75','85'])).

thf('94',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('95',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['92','96'])).

thf('98',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    r2_hidden @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('103',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( r2_hidden @ ( k3_tarski @ sk_A ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['103','104'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('106',plain,(
    ! [X30: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X30 ) )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('107',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['0','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TE8uN20z9J
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:05:12 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.79/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.00  % Solved by: fo/fo7.sh
% 0.79/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.00  % done 409 iterations in 0.544s
% 0.79/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.00  % SZS output start Refutation
% 0.79/1.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.79/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.00  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.79/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/1.00  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.79/1.00  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.79/1.00  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.79/1.00  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.79/1.00  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.79/1.00  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.79/1.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.79/1.00  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.79/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/1.00  thf(v2_yellow_0_type, type, v2_yellow_0: $i > $o).
% 0.79/1.00  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.79/1.00  thf(sk_B_type, type, sk_B: $i > $i).
% 0.79/1.00  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.79/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/1.00  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.79/1.00  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.79/1.00  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.79/1.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.79/1.00  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.79/1.00  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.79/1.00  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.79/1.00  thf(t15_yellow_1, conjecture,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.79/1.00       ( ( v2_yellow_0 @ ( k2_yellow_1 @ A ) ) =>
% 0.79/1.00         ( r2_hidden @ ( k3_tarski @ A ) @ A ) ) ))).
% 0.79/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.00    (~( ![A:$i]:
% 0.79/1.00        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.79/1.00          ( ( v2_yellow_0 @ ( k2_yellow_1 @ A ) ) =>
% 0.79/1.00            ( r2_hidden @ ( k3_tarski @ A ) @ A ) ) ) )),
% 0.79/1.00    inference('cnf.neg', [status(esa)], [t15_yellow_1])).
% 0.79/1.00  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf(d4_tarski, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.79/1.00       ( ![C:$i]:
% 0.79/1.00         ( ( r2_hidden @ C @ B ) <=>
% 0.79/1.00           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.79/1.00  thf('1', plain,
% 0.79/1.00      (![X5 : $i, X9 : $i]:
% 0.79/1.00         (((X9) = (k3_tarski @ X5))
% 0.79/1.00          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ (sk_D @ X9 @ X5))
% 0.79/1.00          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('2', plain, ((v2_yellow_0 @ (k2_yellow_1 @ sk_A))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf(t1_yellow_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.79/1.00       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.79/1.00  thf('3', plain, (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.79/1.00  thf(d5_yellow_0, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( l1_orders_2 @ A ) =>
% 0.79/1.00       ( ( v2_yellow_0 @ A ) <=>
% 0.79/1.00         ( ?[B:$i]:
% 0.79/1.00           ( ( r2_lattice3 @ A @ ( u1_struct_0 @ A ) @ B ) & 
% 0.79/1.00             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.79/1.00  thf('4', plain,
% 0.79/1.00      (![X22 : $i]:
% 0.79/1.00         (~ (v2_yellow_0 @ X22)
% 0.79/1.00          | (m1_subset_1 @ (sk_B @ X22) @ (u1_struct_0 @ X22))
% 0.79/1.00          | ~ (l1_orders_2 @ X22))),
% 0.79/1.00      inference('cnf', [status(esa)], [d5_yellow_0])).
% 0.79/1.00  thf('5', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ X0)) @ X0)
% 0.79/1.00          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.79/1.00          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.79/1.00      inference('sup+', [status(thm)], ['3', '4'])).
% 0.79/1.00  thf(dt_k2_yellow_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.79/1.00       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.79/1.00  thf('6', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 0.79/1.00      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.79/1.00  thf('7', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ X0)) @ X0)
% 0.79/1.00          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.79/1.00      inference('demod', [status(thm)], ['5', '6'])).
% 0.79/1.00  thf('8', plain, ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.79/1.00      inference('sup-', [status(thm)], ['2', '7'])).
% 0.79/1.00  thf(t2_subset, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( m1_subset_1 @ A @ B ) =>
% 0.79/1.00       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.79/1.00  thf('9', plain,
% 0.79/1.00      (![X13 : $i, X14 : $i]:
% 0.79/1.00         ((r2_hidden @ X13 @ X14)
% 0.79/1.00          | (v1_xboole_0 @ X14)
% 0.79/1.00          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.79/1.00      inference('cnf', [status(esa)], [t2_subset])).
% 0.79/1.00  thf('10', plain,
% 0.79/1.00      (((v1_xboole_0 @ sk_A)
% 0.79/1.00        | (r2_hidden @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.79/1.00  thf('11', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('12', plain, ((r2_hidden @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.79/1.00      inference('clc', [status(thm)], ['10', '11'])).
% 0.79/1.00  thf('13', plain,
% 0.79/1.00      (![X5 : $i, X9 : $i]:
% 0.79/1.00         (((X9) = (k3_tarski @ X5))
% 0.79/1.00          | (r2_hidden @ (sk_D @ X9 @ X5) @ X5)
% 0.79/1.00          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('14', plain,
% 0.79/1.00      (![X5 : $i, X9 : $i]:
% 0.79/1.00         (((X9) = (k3_tarski @ X5))
% 0.79/1.00          | (r2_hidden @ (sk_D @ X9 @ X5) @ X5)
% 0.79/1.00          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('15', plain,
% 0.79/1.00      (![X5 : $i, X9 : $i, X10 : $i]:
% 0.79/1.00         (((X9) = (k3_tarski @ X5))
% 0.79/1.00          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X10)
% 0.79/1.00          | ~ (r2_hidden @ X10 @ X5)
% 0.79/1.00          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('16', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 0.79/1.00          | ((X0) = (k3_tarski @ X1))
% 0.79/1.00          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 0.79/1.00          | ~ (r2_hidden @ X0 @ X1)
% 0.79/1.00          | ((X0) = (k3_tarski @ X1)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['14', '15'])).
% 0.79/1.00  thf('17', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X0 @ X1)
% 0.79/1.00          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 0.79/1.00          | ((X0) = (k3_tarski @ X1))
% 0.79/1.00          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1))),
% 0.79/1.00      inference('simplify', [status(thm)], ['16'])).
% 0.79/1.00  thf('18', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 0.79/1.00          | ((X0) = (k3_tarski @ X1))
% 0.79/1.00          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 0.79/1.00          | ((X0) = (k3_tarski @ X1))
% 0.79/1.00          | ~ (r2_hidden @ X0 @ X1))),
% 0.79/1.00      inference('sup-', [status(thm)], ['13', '17'])).
% 0.79/1.00  thf('19', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X0 @ X1)
% 0.79/1.00          | ((X0) = (k3_tarski @ X1))
% 0.79/1.00          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1))),
% 0.79/1.00      inference('simplify', [status(thm)], ['18'])).
% 0.79/1.00  thf('20', plain,
% 0.79/1.00      (((r2_hidden @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A)
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['12', '19'])).
% 0.79/1.00  thf(t1_subset, axiom,
% 0.79/1.00    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.79/1.00  thf('21', plain,
% 0.79/1.00      (![X11 : $i, X12 : $i]:
% 0.79/1.00         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_subset])).
% 0.79/1.00  thf('22', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['20', '21'])).
% 0.79/1.00  thf('23', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['20', '21'])).
% 0.79/1.00  thf('24', plain,
% 0.79/1.00      (((r2_hidden @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A)
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['12', '19'])).
% 0.79/1.00  thf('25', plain, ((v2_yellow_0 @ (k2_yellow_1 @ sk_A))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('26', plain,
% 0.79/1.00      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.79/1.00  thf('27', plain,
% 0.79/1.00      (![X22 : $i]:
% 0.79/1.00         (~ (v2_yellow_0 @ X22)
% 0.79/1.00          | (r2_lattice3 @ X22 @ (u1_struct_0 @ X22) @ (sk_B @ X22))
% 0.79/1.00          | ~ (l1_orders_2 @ X22))),
% 0.79/1.00      inference('cnf', [status(esa)], [d5_yellow_0])).
% 0.79/1.00  thf('28', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((r2_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ (sk_B @ (k2_yellow_1 @ X0)))
% 0.79/1.00          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.79/1.00          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.79/1.00      inference('sup+', [status(thm)], ['26', '27'])).
% 0.79/1.00  thf('29', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 0.79/1.00      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.79/1.00  thf('30', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((r2_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ (sk_B @ (k2_yellow_1 @ X0)))
% 0.79/1.00          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.79/1.00      inference('demod', [status(thm)], ['28', '29'])).
% 0.79/1.00  thf('31', plain,
% 0.79/1.00      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ 
% 0.79/1.00        (sk_B @ (k2_yellow_1 @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['25', '30'])).
% 0.79/1.00  thf('32', plain,
% 0.79/1.00      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.79/1.00  thf(d9_lattice3, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( l1_orders_2 @ A ) =>
% 0.79/1.00       ( ![B:$i,C:$i]:
% 0.79/1.00         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.79/1.00           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.79/1.00             ( ![D:$i]:
% 0.79/1.00               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.79/1.00                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.79/1.00  thf('33', plain,
% 0.79/1.00      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.79/1.00          | ~ (r2_lattice3 @ X19 @ X20 @ X18)
% 0.79/1.00          | ~ (r2_hidden @ X21 @ X20)
% 0.79/1.00          | (r1_orders_2 @ X19 @ X21 @ X18)
% 0.79/1.00          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.79/1.00          | ~ (l1_orders_2 @ X19))),
% 0.79/1.00      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.79/1.00  thf('34', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X1 @ X0)
% 0.79/1.00          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.79/1.00          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.79/1.00          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.79/1.00          | ~ (r2_hidden @ X2 @ X3)
% 0.79/1.00          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X3 @ X1))),
% 0.79/1.00      inference('sup-', [status(thm)], ['32', '33'])).
% 0.79/1.00  thf('35', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 0.79/1.00      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.79/1.00  thf('36', plain,
% 0.79/1.00      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.79/1.00  thf('37', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X1 @ X0)
% 0.79/1.00          | ~ (m1_subset_1 @ X2 @ X0)
% 0.79/1.00          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.79/1.00          | ~ (r2_hidden @ X2 @ X3)
% 0.79/1.00          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X3 @ X1))),
% 0.79/1.00      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.79/1.00  thf('38', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X0 @ sk_A)
% 0.79/1.00          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 0.79/1.00             (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.79/1.00          | ~ (m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['31', '37'])).
% 0.79/1.00  thf('39', plain, ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.79/1.00      inference('sup-', [status(thm)], ['2', '7'])).
% 0.79/1.00  thf('40', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X0 @ sk_A)
% 0.79/1.00          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 0.79/1.00             (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.79/1.00      inference('demod', [status(thm)], ['38', '39'])).
% 0.79/1.00  thf('41', plain,
% 0.79/1.00      (![X11 : $i, X12 : $i]:
% 0.79/1.00         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_subset])).
% 0.79/1.00  thf('42', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.79/1.00      inference('clc', [status(thm)], ['40', '41'])).
% 0.79/1.00  thf('43', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.79/1.00           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['24', '42'])).
% 0.79/1.00  thf('44', plain,
% 0.79/1.00      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.79/1.00  thf(redefinition_r3_orders_2, axiom,
% 0.79/1.00    (![A:$i,B:$i,C:$i]:
% 0.79/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.79/1.00         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.79/1.00         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.79/1.00       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.79/1.00  thf('45', plain,
% 0.79/1.00      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.79/1.00          | ~ (l1_orders_2 @ X16)
% 0.79/1.00          | ~ (v3_orders_2 @ X16)
% 0.79/1.00          | (v2_struct_0 @ X16)
% 0.79/1.00          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.79/1.00          | (r3_orders_2 @ X16 @ X15 @ X17)
% 0.79/1.00          | ~ (r1_orders_2 @ X16 @ X15 @ X17))),
% 0.79/1.00      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.79/1.00  thf('46', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X1 @ X0)
% 0.79/1.00          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.79/1.00          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.79/1.00          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.79/1.00          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.79/1.00          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.79/1.00          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['44', '45'])).
% 0.79/1.00  thf('47', plain,
% 0.79/1.00      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.79/1.00  thf(fc5_yellow_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.79/1.00       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.79/1.00       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.79/1.00       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.79/1.00  thf('48', plain, (![X27 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X27))),
% 0.79/1.00      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.79/1.00  thf('49', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 0.79/1.00      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.79/1.00  thf('50', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X1 @ X0)
% 0.79/1.00          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.79/1.00          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.79/1.00          | ~ (m1_subset_1 @ X2 @ X0)
% 0.79/1.00          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.79/1.00      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.79/1.00  thf('51', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | ~ (m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.79/1.00        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.79/1.00           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ~ (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['43', '50'])).
% 0.79/1.00  thf('52', plain, ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.79/1.00      inference('sup-', [status(thm)], ['2', '7'])).
% 0.79/1.00  thf('53', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.79/1.00           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ~ (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.79/1.00      inference('demod', [status(thm)], ['51', '52'])).
% 0.79/1.00  thf('54', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.79/1.00           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['23', '53'])).
% 0.79/1.00  thf('55', plain,
% 0.79/1.00      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.79/1.00           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('simplify', [status(thm)], ['54'])).
% 0.79/1.00  thf(t3_yellow_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.79/1.00       ( ![B:$i]:
% 0.79/1.00         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.79/1.00           ( ![C:$i]:
% 0.79/1.00             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.79/1.00               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.79/1.00                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.79/1.00  thf('56', plain,
% 0.79/1.00      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ (k2_yellow_1 @ X34)))
% 0.79/1.00          | ~ (r3_orders_2 @ (k2_yellow_1 @ X34) @ X33 @ X35)
% 0.79/1.00          | (r1_tarski @ X33 @ X35)
% 0.79/1.00          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ (k2_yellow_1 @ X34)))
% 0.79/1.00          | (v1_xboole_0 @ X34))),
% 0.79/1.00      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.79/1.00  thf('57', plain,
% 0.79/1.00      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.79/1.00  thf('58', plain,
% 0.79/1.00      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.79/1.00  thf('59', plain,
% 0.79/1.00      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.79/1.00         (~ (m1_subset_1 @ X33 @ X34)
% 0.79/1.00          | ~ (r3_orders_2 @ (k2_yellow_1 @ X34) @ X33 @ X35)
% 0.79/1.00          | (r1_tarski @ X33 @ X35)
% 0.79/1.00          | ~ (m1_subset_1 @ X35 @ X34)
% 0.79/1.00          | (v1_xboole_0 @ X34))),
% 0.79/1.00      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.79/1.00  thf('60', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | (v1_xboole_0 @ sk_A)
% 0.79/1.00        | ~ (m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.79/1.00        | (r1_tarski @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ~ (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['55', '59'])).
% 0.79/1.00  thf('61', plain, ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.79/1.00      inference('sup-', [status(thm)], ['2', '7'])).
% 0.79/1.00  thf('62', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | (v1_xboole_0 @ sk_A)
% 0.79/1.00        | (r1_tarski @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ~ (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.79/1.00      inference('demod', [status(thm)], ['60', '61'])).
% 0.79/1.00  thf('63', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r1_tarski @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | (v1_xboole_0 @ sk_A)
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['22', '62'])).
% 0.79/1.00  thf('64', plain,
% 0.79/1.00      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | (v1_xboole_0 @ sk_A)
% 0.79/1.00        | (r1_tarski @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('simplify', [status(thm)], ['63'])).
% 0.79/1.00  thf(d3_tarski, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( r1_tarski @ A @ B ) <=>
% 0.79/1.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.79/1.00  thf('65', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X0 @ X1)
% 0.79/1.00          | (r2_hidden @ X0 @ X2)
% 0.79/1.00          | ~ (r1_tarski @ X1 @ X2))),
% 0.79/1.00      inference('cnf', [status(esa)], [d3_tarski])).
% 0.79/1.00  thf('66', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         (((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00          | (v1_xboole_0 @ sk_A)
% 0.79/1.00          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00          | (r2_hidden @ X0 @ (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['64', '65'])).
% 0.79/1.00  thf('67', plain,
% 0.79/1.00      (((r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00         (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | (v1_xboole_0 @ sk_A)
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['1', '66'])).
% 0.79/1.00  thf('68', plain,
% 0.79/1.00      (((v1_xboole_0 @ sk_A)
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.79/1.00      inference('simplify', [status(thm)], ['67'])).
% 0.79/1.00  thf('69', plain,
% 0.79/1.00      (((r2_hidden @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A)
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['12', '19'])).
% 0.79/1.00  thf('70', plain,
% 0.79/1.00      (![X5 : $i, X9 : $i]:
% 0.79/1.00         (((X9) = (k3_tarski @ X5))
% 0.79/1.00          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ (sk_D @ X9 @ X5))
% 0.79/1.00          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('71', plain,
% 0.79/1.00      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X4 @ X5)
% 0.79/1.00          | ~ (r2_hidden @ X6 @ X4)
% 0.79/1.00          | (r2_hidden @ X6 @ X7)
% 0.79/1.00          | ((X7) != (k3_tarski @ X5)))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('72', plain,
% 0.79/1.00      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.79/1.00         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.79/1.00          | ~ (r2_hidden @ X6 @ X4)
% 0.79/1.00          | ~ (r2_hidden @ X4 @ X5))),
% 0.79/1.00      inference('simplify', [status(thm)], ['71'])).
% 0.79/1.00  thf('73', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.00         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.79/1.00          | ((X1) = (k3_tarski @ X0))
% 0.79/1.00          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 0.79/1.00          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['70', '72'])).
% 0.79/1.00  thf('74', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (k3_tarski @ sk_A))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['69', '73'])).
% 0.79/1.00  thf('75', plain,
% 0.79/1.00      (((r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00         (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (k3_tarski @ sk_A))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('simplify', [status(thm)], ['74'])).
% 0.79/1.00  thf('76', plain, ((r2_hidden @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.79/1.00      inference('clc', [status(thm)], ['10', '11'])).
% 0.79/1.00  thf('77', plain,
% 0.79/1.00      (![X1 : $i, X3 : $i]:
% 0.79/1.00         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.79/1.00      inference('cnf', [status(esa)], [d3_tarski])).
% 0.79/1.00  thf('78', plain,
% 0.79/1.00      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.79/1.00         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.79/1.00          | ~ (r2_hidden @ X6 @ X4)
% 0.79/1.00          | ~ (r2_hidden @ X4 @ X5))),
% 0.79/1.00      inference('simplify', [status(thm)], ['71'])).
% 0.79/1.00  thf('79', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.00         ((r1_tarski @ X0 @ X1)
% 0.79/1.00          | ~ (r2_hidden @ X0 @ X2)
% 0.79/1.00          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['77', '78'])).
% 0.79/1.00  thf('80', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((r2_hidden @ (sk_C @ X0 @ (sk_B @ (k2_yellow_1 @ sk_A))) @ 
% 0.79/1.00           (k3_tarski @ sk_A))
% 0.79/1.00          | (r1_tarski @ (sk_B @ (k2_yellow_1 @ sk_A)) @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['76', '79'])).
% 0.79/1.00  thf('81', plain,
% 0.79/1.00      (![X1 : $i, X3 : $i]:
% 0.79/1.00         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.79/1.00      inference('cnf', [status(esa)], [d3_tarski])).
% 0.79/1.00  thf('82', plain,
% 0.79/1.00      (((r1_tarski @ (sk_B @ (k2_yellow_1 @ sk_A)) @ (k3_tarski @ sk_A))
% 0.79/1.00        | (r1_tarski @ (sk_B @ (k2_yellow_1 @ sk_A)) @ (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['80', '81'])).
% 0.79/1.00  thf('83', plain,
% 0.79/1.00      ((r1_tarski @ (sk_B @ (k2_yellow_1 @ sk_A)) @ (k3_tarski @ sk_A))),
% 0.79/1.00      inference('simplify', [status(thm)], ['82'])).
% 0.79/1.00  thf('84', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X0 @ X1)
% 0.79/1.00          | (r2_hidden @ X0 @ X2)
% 0.79/1.00          | ~ (r1_tarski @ X1 @ X2))),
% 0.79/1.00      inference('cnf', [status(esa)], [d3_tarski])).
% 0.79/1.00  thf('85', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((r2_hidden @ X0 @ (k3_tarski @ sk_A))
% 0.79/1.00          | ~ (r2_hidden @ X0 @ (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['83', '84'])).
% 0.79/1.00  thf('86', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('clc', [status(thm)], ['75', '85'])).
% 0.79/1.00  thf('87', plain,
% 0.79/1.00      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X8 @ X7)
% 0.79/1.00          | (r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 0.79/1.00          | ((X7) != (k3_tarski @ X5)))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('88', plain,
% 0.79/1.00      (![X5 : $i, X8 : $i]:
% 0.79/1.00         ((r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 0.79/1.00          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 0.79/1.00      inference('simplify', [status(thm)], ['87'])).
% 0.79/1.00  thf('89', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (sk_D_1 @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['86', '88'])).
% 0.79/1.00  thf('90', plain,
% 0.79/1.00      (![X5 : $i, X9 : $i, X10 : $i]:
% 0.79/1.00         (((X9) = (k3_tarski @ X5))
% 0.79/1.00          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X10)
% 0.79/1.00          | ~ (r2_hidden @ X10 @ X5)
% 0.79/1.00          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('91', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | ~ (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00             (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ~ (r2_hidden @ 
% 0.79/1.00             (sk_D_1 @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A) @ 
% 0.79/1.00             sk_A)
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['89', '90'])).
% 0.79/1.00  thf('92', plain,
% 0.79/1.00      ((~ (r2_hidden @ 
% 0.79/1.00           (sk_D_1 @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A) @ 
% 0.79/1.00           sk_A)
% 0.79/1.00        | ~ (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00             (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('simplify', [status(thm)], ['91'])).
% 0.79/1.00  thf('93', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00           (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('clc', [status(thm)], ['75', '85'])).
% 0.79/1.00  thf('94', plain,
% 0.79/1.00      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X8 @ X7)
% 0.79/1.00          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 0.79/1.00          | ((X7) != (k3_tarski @ X5)))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_tarski])).
% 0.79/1.00  thf('95', plain,
% 0.79/1.00      (![X5 : $i, X8 : $i]:
% 0.79/1.00         ((r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 0.79/1.00          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 0.79/1.00      inference('simplify', [status(thm)], ['94'])).
% 0.79/1.00  thf('96', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (r2_hidden @ 
% 0.79/1.00           (sk_D_1 @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A) @ 
% 0.79/1.00           sk_A))),
% 0.79/1.00      inference('sup-', [status(thm)], ['93', '95'])).
% 0.79/1.00  thf('97', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | ~ (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.79/1.00             (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.79/1.00      inference('clc', [status(thm)], ['92', '96'])).
% 0.79/1.00  thf('98', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | (v1_xboole_0 @ sk_A)
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['68', '97'])).
% 0.79/1.00  thf('99', plain,
% 0.79/1.00      (((v1_xboole_0 @ sk_A)
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.79/1.00        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.79/1.00      inference('simplify', [status(thm)], ['98'])).
% 0.79/1.00  thf('100', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('101', plain,
% 0.79/1.00      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.79/1.00      inference('clc', [status(thm)], ['99', '100'])).
% 0.79/1.00  thf('102', plain, ((r2_hidden @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.79/1.00      inference('clc', [status(thm)], ['10', '11'])).
% 0.79/1.00  thf('103', plain,
% 0.79/1.00      (((r2_hidden @ (k3_tarski @ sk_A) @ sk_A)
% 0.79/1.00        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.79/1.00      inference('sup+', [status(thm)], ['101', '102'])).
% 0.79/1.00  thf('104', plain, (~ (r2_hidden @ (k3_tarski @ sk_A) @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('105', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.79/1.00      inference('clc', [status(thm)], ['103', '104'])).
% 0.79/1.00  thf(fc6_yellow_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.79/1.00       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.79/1.00         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.79/1.00  thf('106', plain,
% 0.79/1.00      (![X30 : $i]:
% 0.79/1.00         (~ (v2_struct_0 @ (k2_yellow_1 @ X30)) | (v1_xboole_0 @ X30))),
% 0.79/1.00      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.79/1.00  thf('107', plain, ((v1_xboole_0 @ sk_A)),
% 0.79/1.00      inference('sup-', [status(thm)], ['105', '106'])).
% 0.79/1.00  thf('108', plain, ($false), inference('demod', [status(thm)], ['0', '107'])).
% 0.79/1.00  
% 0.79/1.00  % SZS output end Refutation
% 0.79/1.00  
% 0.79/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
