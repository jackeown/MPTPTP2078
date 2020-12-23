%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3VQO4TvlOw

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:28 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 332 expanded)
%              Number of leaves         :   34 ( 109 expanded)
%              Depth                    :   21
%              Number of atoms          : 1748 (5344 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t38_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ B @ C )
             => ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) )
                & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( r2_hidden @ B @ C )
               => ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) )
                  & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_lattice3])).

thf('0',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('3',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d21_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
           => ( ( C
                = ( k15_lattice3 @ A @ B ) )
            <=> ( ( r4_lattice3 @ A @ C @ B )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r4_lattice3 @ A @ D @ B )
                     => ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( X15
       != ( k15_lattice3 @ X14 @ X16 ) )
      | ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('7',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r4_lattice3 @ X14 @ ( k15_lattice3 @ X14 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X14 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d17_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r4_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X9 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_lattices @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_lattices @ A @ B @ C )
      <=> ( r1_lattices @ A @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v9_lattices @ X2 )
      | ~ ( v8_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r3_lattices @ X2 @ X1 @ X3 )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','32','38','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','49'])).

thf('51',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
   <= ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','58'])).

thf(d22_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k16_lattice3 @ A @ B )
          = ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) )).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k16_lattice3 @ X18 @ X19 )
        = ( k15_lattice3 @ X18 @ ( a_2_1_lattice3 @ X18 @ X19 ) ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('61',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X13 )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf(fraenkel_a_2_1_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r3_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('70',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( X24
        = ( sk_D_3 @ X23 @ X22 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ ( a_2_1_lattice3 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('73',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( r3_lattice3 @ X22 @ ( sk_D_3 @ X23 @ X22 @ X24 ) @ X23 )
      | ~ ( r2_hidden @ X24 @ ( a_2_1_lattice3 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf(d16_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r3_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','87'])).

thf('89',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','91'])).

thf('93',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_lattices @ X10 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X9 )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['93','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('106',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( X15
       != ( k15_lattice3 @ X14 @ X16 ) )
      | ~ ( r4_lattice3 @ X14 @ X17 @ X16 )
      | ( r1_lattices @ X14 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('107',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_lattices @ X14 @ ( k15_lattice3 @ X14 @ X16 ) @ X17 )
      | ~ ( r4_lattice3 @ X14 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X14 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['103','116'])).

thf('118',plain,
    ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['60','117'])).

thf('119',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k16_lattice3 @ X18 @ X19 )
        = ( k15_lattice3 @ X18 @ ( a_2_1_lattice3 @ X18 @ X19 ) ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('125',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v9_lattices @ X2 )
      | ~ ( v8_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r3_lattices @ X2 @ X1 @ X3 )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','130'])).

thf('132',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('134',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('135',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['122','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['59','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3VQO4TvlOw
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 272 iterations in 0.254s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.50/0.71  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.50/0.71  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.50/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.71  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.50/0.71  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.50/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.71  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.50/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.71  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.50/0.71  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.50/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.50/0.71  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.50/0.71  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.50/0.71  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.50/0.71  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.50/0.71  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.50/0.71  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.50/0.71  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.50/0.71  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.50/0.71  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.50/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.71  thf(t38_lattice3, conjecture,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.50/0.71         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( r2_hidden @ B @ C ) =>
% 0.50/0.71               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.50/0.71                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i]:
% 0.50/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.50/0.71            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.50/0.71          ( ![B:$i]:
% 0.50/0.71            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.71              ( ![C:$i]:
% 0.50/0.71                ( ( r2_hidden @ B @ C ) =>
% 0.50/0.71                  ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.50/0.71                    ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t38_lattice3])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      ((~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.50/0.71        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))
% 0.50/0.71         <= (~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf(dt_k15_lattice3, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.50/0.71       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         (~ (l3_lattices @ X20)
% 0.50/0.71          | (v2_struct_0 @ X20)
% 0.50/0.71          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.50/0.71  thf('3', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         (~ (l3_lattices @ X20)
% 0.50/0.71          | (v2_struct_0 @ X20)
% 0.50/0.71          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.50/0.71  thf(d21_lattice3, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.50/0.71       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.50/0.71           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.50/0.71         ( ![B:$i,C:$i]:
% 0.50/0.71           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.71             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.50/0.71               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.50/0.71                 ( ![D:$i]:
% 0.50/0.71                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.71                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.50/0.71                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X14)
% 0.50/0.71          | ~ (v10_lattices @ X14)
% 0.50/0.71          | ~ (v4_lattice3 @ X14)
% 0.50/0.71          | ~ (l3_lattices @ X14)
% 0.50/0.71          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.50/0.71          | ((X15) != (k15_lattice3 @ X14 @ X16))
% 0.50/0.71          | (r4_lattice3 @ X14 @ X15 @ X16)
% 0.50/0.71          | ~ (l3_lattices @ X14)
% 0.50/0.71          | (v2_struct_0 @ X14))),
% 0.50/0.71      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      (![X14 : $i, X16 : $i]:
% 0.50/0.71         ((r4_lattice3 @ X14 @ (k15_lattice3 @ X14 @ X16) @ X16)
% 0.50/0.71          | ~ (m1_subset_1 @ (k15_lattice3 @ X14 @ X16) @ (u1_struct_0 @ X14))
% 0.50/0.71          | ~ (l3_lattices @ X14)
% 0.50/0.71          | ~ (v4_lattice3 @ X14)
% 0.50/0.71          | ~ (v10_lattices @ X14)
% 0.50/0.71          | (v2_struct_0 @ X14))),
% 0.50/0.71      inference('simplify', [status(thm)], ['6'])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v10_lattices @ X0)
% 0.50/0.71          | ~ (v4_lattice3 @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['5', '7'])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1)
% 0.50/0.71          | ~ (v4_lattice3 @ X0)
% 0.50/0.71          | ~ (v10_lattices @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['8'])).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         (~ (l3_lattices @ X20)
% 0.50/0.71          | (v2_struct_0 @ X20)
% 0.50/0.71          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.50/0.71  thf(d17_lattice3, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.50/0.71               ( ![D:$i]:
% 0.50/0.71                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.71                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf('11', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.50/0.71          | ~ (r4_lattice3 @ X10 @ X9 @ X11)
% 0.50/0.71          | ~ (r2_hidden @ X12 @ X11)
% 0.50/0.71          | (r1_lattices @ X10 @ X12 @ X9)
% 0.50/0.71          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.50/0.71          | ~ (l3_lattices @ X10)
% 0.50/0.71          | (v2_struct_0 @ X10))),
% 0.50/0.71      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.50/0.71          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.50/0.71          | ~ (r2_hidden @ X2 @ X3)
% 0.50/0.71          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 0.50/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 0.50/0.71          | ~ (r2_hidden @ X2 @ X3)
% 0.50/0.71          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.50/0.71          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['12'])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X1)
% 0.50/0.71          | ~ (l3_lattices @ X1)
% 0.50/0.71          | ~ (v10_lattices @ X1)
% 0.50/0.71          | ~ (v4_lattice3 @ X1)
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | ~ (l3_lattices @ X1)
% 0.50/0.71          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.50/0.71          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.50/0.71          | ~ (r2_hidden @ X2 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['9', '13'])).
% 0.50/0.71  thf('15', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X2 @ X0)
% 0.50/0.71          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.50/0.71          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.50/0.71          | ~ (v4_lattice3 @ X1)
% 0.50/0.71          | ~ (v10_lattices @ X1)
% 0.50/0.71          | ~ (l3_lattices @ X1)
% 0.50/0.71          | (v2_struct_0 @ X1))),
% 0.50/0.71      inference('simplify', [status(thm)], ['14'])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (l3_lattices @ sk_A)
% 0.50/0.71          | ~ (v10_lattices @ sk_A)
% 0.50/0.71          | ~ (v4_lattice3 @ sk_A)
% 0.50/0.71          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.50/0.71          | ~ (r2_hidden @ sk_B @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['4', '15'])).
% 0.50/0.71  thf('17', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('18', plain, ((v10_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('19', plain, ((v4_lattice3 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('20', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.50/0.71          | ~ (r2_hidden @ sk_B @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.50/0.71  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r2_hidden @ sk_B @ X0)
% 0.50/0.71          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.50/0.71      inference('clc', [status(thm)], ['20', '21'])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      ((r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.50/0.71      inference('sup-', [status(thm)], ['3', '22'])).
% 0.50/0.71  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(redefinition_r3_lattices, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.50/0.71         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.50/0.71         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.50/0.71         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.71       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.50/0.71          | ~ (l3_lattices @ X2)
% 0.50/0.71          | ~ (v9_lattices @ X2)
% 0.50/0.71          | ~ (v8_lattices @ X2)
% 0.50/0.71          | ~ (v6_lattices @ X2)
% 0.50/0.71          | (v2_struct_0 @ X2)
% 0.50/0.71          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.50/0.71          | (r3_lattices @ X2 @ X1 @ X3)
% 0.50/0.71          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r1_lattices @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (r3_lattices @ sk_A @ sk_B @ X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.50/0.71          | (v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (v6_lattices @ sk_A)
% 0.50/0.71          | ~ (v8_lattices @ sk_A)
% 0.50/0.71          | ~ (v9_lattices @ sk_A)
% 0.50/0.71          | ~ (l3_lattices @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.71  thf(cc1_lattices, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l3_lattices @ A ) =>
% 0.50/0.71       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.50/0.71         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.50/0.71           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.50/0.71           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.50/0.71  thf('27', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v10_lattices @ X0)
% 0.50/0.71          | (v6_lattices @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.50/0.71  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('31', plain, ((v10_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('32', plain, ((v6_lattices @ sk_A)),
% 0.50/0.71      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v10_lattices @ X0)
% 0.50/0.71          | (v8_lattices @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.50/0.71  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.71  thf('36', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('37', plain, ((v10_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('38', plain, ((v8_lattices @ sk_A)),
% 0.50/0.71      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.50/0.71  thf('39', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v10_lattices @ X0)
% 0.50/0.71          | (v9_lattices @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.50/0.71  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('41', plain,
% 0.50/0.71      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.50/0.71  thf('42', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('43', plain, ((v10_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('44', plain, ((v9_lattices @ sk_A)),
% 0.50/0.71      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.50/0.71  thf('45', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('46', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r1_lattices @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (r3_lattices @ sk_A @ sk_B @ X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.50/0.71          | (v2_struct_0 @ sk_A))),
% 0.50/0.71      inference('demod', [status(thm)], ['26', '32', '38', '44', '45'])).
% 0.50/0.71  thf('47', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_A)
% 0.50/0.71        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.50/0.71        | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['23', '46'])).
% 0.50/0.71  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('49', plain,
% 0.50/0.71      (((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.50/0.71        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('clc', [status(thm)], ['47', '48'])).
% 0.50/0.71  thf('50', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_A)
% 0.50/0.71        | ~ (l3_lattices @ sk_A)
% 0.50/0.71        | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['2', '49'])).
% 0.50/0.71  thf('51', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('52', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_A)
% 0.50/0.71        | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '51'])).
% 0.50/0.71  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('54', plain,
% 0.50/0.71      ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.50/0.71      inference('clc', [status(thm)], ['52', '53'])).
% 0.50/0.71  thf('55', plain,
% 0.50/0.71      ((~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))
% 0.50/0.71         <= (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('56', plain,
% 0.50/0.71      (((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.50/0.71  thf('57', plain,
% 0.50/0.71      (~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)) | 
% 0.50/0.71       ~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('58', plain,
% 0.50/0.71      (~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.50/0.71      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.50/0.71  thf('59', plain,
% 0.50/0.71      (~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.50/0.71      inference('simpl_trail', [status(thm)], ['1', '58'])).
% 0.50/0.71  thf(d22_lattice3, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( k16_lattice3 @ A @ B ) =
% 0.50/0.71           ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) ))).
% 0.50/0.71  thf('60', plain,
% 0.50/0.71      (![X18 : $i, X19 : $i]:
% 0.50/0.71         (((k16_lattice3 @ X18 @ X19)
% 0.50/0.71            = (k15_lattice3 @ X18 @ (a_2_1_lattice3 @ X18 @ X19)))
% 0.50/0.71          | ~ (l3_lattices @ X18)
% 0.50/0.71          | (v2_struct_0 @ X18))),
% 0.50/0.71      inference('cnf', [status(esa)], [d22_lattice3])).
% 0.50/0.71  thf('61', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('62', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('64', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.50/0.71          | (r2_hidden @ (sk_D_1 @ X13 @ X9 @ X10) @ X13)
% 0.50/0.71          | (r4_lattice3 @ X10 @ X9 @ X13)
% 0.50/0.71          | ~ (l3_lattices @ X10)
% 0.50/0.71          | (v2_struct_0 @ X10))),
% 0.50/0.71      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.50/0.71  thf('65', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (l3_lattices @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['63', '64'])).
% 0.50/0.71  thf('66', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('67', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['65', '66'])).
% 0.50/0.71  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('69', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.50/0.71      inference('clc', [status(thm)], ['67', '68'])).
% 0.50/0.71  thf(fraenkel_a_2_1_lattice3, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.50/0.71       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 0.50/0.71         ( ?[D:$i]:
% 0.50/0.71           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.50/0.71             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.50/0.71  thf('70', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         (~ (l3_lattices @ X22)
% 0.50/0.71          | (v2_struct_0 @ X22)
% 0.50/0.71          | ((X24) = (sk_D_3 @ X23 @ X22 @ X24))
% 0.50/0.71          | ~ (r2_hidden @ X24 @ (a_2_1_lattice3 @ X22 @ X23)))),
% 0.50/0.71      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.50/0.71  thf('71', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.50/0.71          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 0.50/0.71              = (sk_D_3 @ X0 @ X1 @ 
% 0.50/0.71                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | ~ (l3_lattices @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['69', '70'])).
% 0.50/0.71  thf('72', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.50/0.71      inference('clc', [status(thm)], ['67', '68'])).
% 0.50/0.71  thf('73', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         (~ (l3_lattices @ X22)
% 0.50/0.71          | (v2_struct_0 @ X22)
% 0.50/0.71          | (r3_lattice3 @ X22 @ (sk_D_3 @ X23 @ X22 @ X24) @ X23)
% 0.50/0.71          | ~ (r2_hidden @ X24 @ (a_2_1_lattice3 @ X22 @ X23)))),
% 0.50/0.71      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.50/0.71  thf('74', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.50/0.71          | (r3_lattice3 @ X1 @ 
% 0.50/0.71             (sk_D_3 @ X0 @ X1 @ 
% 0.50/0.71              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 0.50/0.71             X0)
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | ~ (l3_lattices @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['72', '73'])).
% 0.50/0.71  thf('75', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r3_lattice3 @ X1 @ 
% 0.50/0.71           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X1)
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.50/0.71          | ~ (l3_lattices @ X1)
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['71', '74'])).
% 0.50/0.71  thf('76', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | ~ (l3_lattices @ X1)
% 0.50/0.71          | (r3_lattice3 @ X1 @ 
% 0.50/0.71             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['75'])).
% 0.50/0.71  thf('77', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('78', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.50/0.71          | (m1_subset_1 @ (sk_D_1 @ X13 @ X9 @ X10) @ (u1_struct_0 @ X10))
% 0.50/0.71          | (r4_lattice3 @ X10 @ X9 @ X13)
% 0.50/0.71          | ~ (l3_lattices @ X10)
% 0.50/0.71          | (v2_struct_0 @ X10))),
% 0.50/0.71      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.50/0.71  thf('79', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (l3_lattices @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['77', '78'])).
% 0.50/0.71  thf('80', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('81', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('demod', [status(thm)], ['79', '80'])).
% 0.50/0.71  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('83', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.50/0.71      inference('clc', [status(thm)], ['81', '82'])).
% 0.50/0.71  thf(d16_lattice3, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.50/0.71               ( ![D:$i]:
% 0.50/0.71                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.71                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf('84', plain,
% 0.50/0.71      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.50/0.71          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 0.50/0.71          | ~ (r2_hidden @ X7 @ X6)
% 0.50/0.71          | (r1_lattices @ X5 @ X4 @ X7)
% 0.50/0.71          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.50/0.71          | ~ (l3_lattices @ X5)
% 0.50/0.71          | (v2_struct_0 @ X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.50/0.71  thf('85', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (l3_lattices @ sk_A)
% 0.50/0.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.50/0.71          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.50/0.71          | ~ (r2_hidden @ X1 @ X2)
% 0.50/0.71          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['83', '84'])).
% 0.50/0.71  thf('86', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('87', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.50/0.71          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.50/0.71          | ~ (r2_hidden @ X1 @ X2)
% 0.50/0.71          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.50/0.71      inference('demod', [status(thm)], ['85', '86'])).
% 0.50/0.71  thf('88', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (l3_lattices @ sk_A)
% 0.50/0.71          | (v2_struct_0 @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.50/0.71          | ~ (r2_hidden @ X1 @ X0)
% 0.50/0.71          | (r1_lattices @ sk_A @ 
% 0.50/0.71             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.50/0.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.50/0.71          | (v2_struct_0 @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['76', '87'])).
% 0.50/0.71  thf('89', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('90', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.50/0.71          | ~ (r2_hidden @ X1 @ X0)
% 0.50/0.71          | (r1_lattices @ sk_A @ 
% 0.50/0.71             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.50/0.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.50/0.71          | (v2_struct_0 @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.50/0.71      inference('demod', [status(thm)], ['88', '89'])).
% 0.50/0.71  thf('91', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.50/0.71          | (r1_lattices @ sk_A @ 
% 0.50/0.71             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.50/0.71          | ~ (r2_hidden @ X1 @ X0)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.50/0.71          | (v2_struct_0 @ sk_A))),
% 0.50/0.71      inference('simplify', [status(thm)], ['90'])).
% 0.50/0.71  thf('92', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.50/0.71          | ~ (r2_hidden @ sk_B @ X0)
% 0.50/0.71          | (r1_lattices @ sk_A @ 
% 0.50/0.71             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['62', '91'])).
% 0.50/0.71  thf('93', plain,
% 0.50/0.71      (((r1_lattices @ sk_A @ 
% 0.50/0.71         (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 0.50/0.71        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.50/0.71        | (v2_struct_0 @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['61', '92'])).
% 0.50/0.71  thf('94', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('95', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.50/0.71          | ~ (r1_lattices @ X10 @ (sk_D_1 @ X13 @ X9 @ X10) @ X9)
% 0.50/0.71          | (r4_lattice3 @ X10 @ X9 @ X13)
% 0.50/0.71          | ~ (l3_lattices @ X10)
% 0.50/0.71          | (v2_struct_0 @ X10))),
% 0.50/0.71      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.50/0.71  thf('96', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (l3_lattices @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['94', '95'])).
% 0.50/0.71  thf('97', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('98', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['96', '97'])).
% 0.50/0.71  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('100', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.50/0.71          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.50/0.71      inference('clc', [status(thm)], ['98', '99'])).
% 0.50/0.71  thf('101', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_A)
% 0.50/0.71        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.50/0.71      inference('clc', [status(thm)], ['93', '100'])).
% 0.50/0.71  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('103', plain,
% 0.50/0.71      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.50/0.71      inference('clc', [status(thm)], ['101', '102'])).
% 0.50/0.71  thf('104', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('105', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         (~ (l3_lattices @ X20)
% 0.50/0.71          | (v2_struct_0 @ X20)
% 0.50/0.71          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.50/0.71  thf('106', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X14)
% 0.50/0.71          | ~ (v10_lattices @ X14)
% 0.50/0.71          | ~ (v4_lattice3 @ X14)
% 0.50/0.71          | ~ (l3_lattices @ X14)
% 0.50/0.71          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.50/0.71          | ((X15) != (k15_lattice3 @ X14 @ X16))
% 0.50/0.71          | ~ (r4_lattice3 @ X14 @ X17 @ X16)
% 0.50/0.71          | (r1_lattices @ X14 @ X15 @ X17)
% 0.50/0.71          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.50/0.71          | ~ (l3_lattices @ X14)
% 0.50/0.71          | (v2_struct_0 @ X14))),
% 0.50/0.71      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.50/0.71  thf('107', plain,
% 0.50/0.71      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.50/0.71          | (r1_lattices @ X14 @ (k15_lattice3 @ X14 @ X16) @ X17)
% 0.50/0.71          | ~ (r4_lattice3 @ X14 @ X17 @ X16)
% 0.50/0.71          | ~ (m1_subset_1 @ (k15_lattice3 @ X14 @ X16) @ (u1_struct_0 @ X14))
% 0.50/0.71          | ~ (l3_lattices @ X14)
% 0.50/0.71          | ~ (v4_lattice3 @ X14)
% 0.50/0.71          | ~ (v10_lattices @ X14)
% 0.50/0.71          | (v2_struct_0 @ X14))),
% 0.50/0.71      inference('simplify', [status(thm)], ['106'])).
% 0.50/0.71  thf('108', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v10_lattices @ X0)
% 0.50/0.71          | ~ (v4_lattice3 @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.50/0.71          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.50/0.71          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['105', '107'])).
% 0.50/0.71  thf('109', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.50/0.71          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.50/0.71          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.50/0.71          | ~ (v4_lattice3 @ X0)
% 0.50/0.71          | ~ (v10_lattices @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['108'])).
% 0.50/0.71  thf('110', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (l3_lattices @ sk_A)
% 0.50/0.71          | ~ (v10_lattices @ sk_A)
% 0.50/0.71          | ~ (v4_lattice3 @ sk_A)
% 0.50/0.71          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['104', '109'])).
% 0.50/0.71  thf('111', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('112', plain, ((v10_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('113', plain, ((v4_lattice3 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('114', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.50/0.71          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.50/0.71  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('116', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.50/0.71          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.50/0.71      inference('clc', [status(thm)], ['114', '115'])).
% 0.50/0.71  thf('117', plain,
% 0.50/0.71      ((r1_lattices @ sk_A @ 
% 0.50/0.71        (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B)),
% 0.50/0.71      inference('sup-', [status(thm)], ['103', '116'])).
% 0.50/0.71  thf('118', plain,
% 0.50/0.71      (((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)
% 0.50/0.71        | (v2_struct_0 @ sk_A)
% 0.50/0.71        | ~ (l3_lattices @ sk_A))),
% 0.50/0.71      inference('sup+', [status(thm)], ['60', '117'])).
% 0.50/0.71  thf('119', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('120', plain,
% 0.50/0.71      (((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)
% 0.50/0.71        | (v2_struct_0 @ sk_A))),
% 0.50/0.71      inference('demod', [status(thm)], ['118', '119'])).
% 0.50/0.71  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('122', plain,
% 0.50/0.71      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.50/0.71      inference('clc', [status(thm)], ['120', '121'])).
% 0.50/0.71  thf('123', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('124', plain,
% 0.50/0.71      (![X18 : $i, X19 : $i]:
% 0.50/0.71         (((k16_lattice3 @ X18 @ X19)
% 0.50/0.71            = (k15_lattice3 @ X18 @ (a_2_1_lattice3 @ X18 @ X19)))
% 0.50/0.71          | ~ (l3_lattices @ X18)
% 0.50/0.71          | (v2_struct_0 @ X18))),
% 0.50/0.71      inference('cnf', [status(esa)], [d22_lattice3])).
% 0.50/0.71  thf('125', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         (~ (l3_lattices @ X20)
% 0.50/0.71          | (v2_struct_0 @ X20)
% 0.50/0.71          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.50/0.71  thf('126', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | ~ (l3_lattices @ X1)
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | ~ (l3_lattices @ X1))),
% 0.50/0.71      inference('sup+', [status(thm)], ['124', '125'])).
% 0.50/0.71  thf('127', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (l3_lattices @ X1)
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | (m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 0.50/0.71      inference('simplify', [status(thm)], ['126'])).
% 0.50/0.71  thf('128', plain,
% 0.50/0.71      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.50/0.71          | ~ (l3_lattices @ X2)
% 0.50/0.71          | ~ (v9_lattices @ X2)
% 0.50/0.71          | ~ (v8_lattices @ X2)
% 0.50/0.71          | ~ (v6_lattices @ X2)
% 0.50/0.71          | (v2_struct_0 @ X2)
% 0.50/0.71          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.50/0.71          | (r3_lattices @ X2 @ X1 @ X3)
% 0.50/0.71          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.50/0.71  thf('129', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.50/0.71          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.50/0.71          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.50/0.71          | (v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v6_lattices @ X0)
% 0.50/0.71          | ~ (v8_lattices @ X0)
% 0.50/0.71          | ~ (v9_lattices @ X0)
% 0.50/0.71          | ~ (l3_lattices @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['127', '128'])).
% 0.50/0.71  thf('130', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (v9_lattices @ X0)
% 0.50/0.71          | ~ (v8_lattices @ X0)
% 0.50/0.71          | ~ (v6_lattices @ X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.50/0.71          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.50/0.71          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.50/0.71          | ~ (l3_lattices @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['129'])).
% 0.50/0.71  thf('131', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (l3_lattices @ sk_A)
% 0.50/0.71          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.50/0.71          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.50/0.71          | ~ (v6_lattices @ sk_A)
% 0.50/0.71          | ~ (v8_lattices @ sk_A)
% 0.50/0.71          | ~ (v9_lattices @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['123', '130'])).
% 0.50/0.71  thf('132', plain, ((l3_lattices @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('133', plain, ((v6_lattices @ sk_A)),
% 0.50/0.71      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.50/0.71  thf('134', plain, ((v8_lattices @ sk_A)),
% 0.50/0.71      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.50/0.71  thf('135', plain, ((v9_lattices @ sk_A)),
% 0.50/0.71      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.50/0.71  thf('136', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_A)
% 0.50/0.71          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.50/0.71          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 0.50/0.71  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('138', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.50/0.71          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.50/0.71      inference('clc', [status(thm)], ['136', '137'])).
% 0.50/0.71  thf('139', plain,
% 0.50/0.71      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.50/0.71      inference('sup-', [status(thm)], ['122', '138'])).
% 0.50/0.71  thf('140', plain, ($false), inference('demod', [status(thm)], ['59', '139'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
