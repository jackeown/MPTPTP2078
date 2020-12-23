%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PRjT34m6NQ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 243 expanded)
%              Number of leaves         :   31 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          : 1006 (3402 expanded)
%              Number of equality atoms :   13 ( 103 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t42_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( r2_hidden @ B @ C )
                & ( r3_lattice3 @ A @ B @ C ) )
             => ( ( k16_lattice3 @ A @ C )
                = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ( r2_hidden @ B @ C )
                  & ( r3_lattice3 @ A @ B @ C ) )
               => ( ( k16_lattice3 @ A @ C )
                  = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('2',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(t34_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( B
                = ( k16_lattice3 @ A @ C ) )
            <=> ( ( r3_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r3_lattice3 @ A @ D @ C )
                     => ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( X10
       != ( k16_lattice3 @ X11 @ X12 ) )
      | ~ ( r3_lattice3 @ X11 @ X13 @ X12 )
      | ( r3_lattices @ X11 @ X13 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v4_lattice3 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ~ ( v4_lattice3 @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r3_lattices @ X11 @ X13 @ ( k16_lattice3 @ X11 @ X12 ) )
      | ~ ( r3_lattice3 @ X11 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v9_lattices @ X3 )
      | ~ ( v8_lattices @ X3 )
      | ~ ( v6_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( r1_lattices @ X3 @ X2 @ X4 )
      | ~ ( r3_lattices @ X3 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','25','31','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_lattice3,axiom,(
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

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r3_lattices @ X16 @ ( k16_lattice3 @ X16 @ X17 ) @ X15 )
      | ~ ( r2_hidden @ X15 @ X17 )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v4_lattice3 @ X16 )
      | ~ ( v10_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('56',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v9_lattices @ X3 )
      | ~ ( v8_lattices @ X3 )
      | ~ ( v6_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( r1_lattices @ X3 @ X2 @ X4 )
      | ~ ( r3_lattices @ X3 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('62',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('63',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['53','66'])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattices @ A @ B @ C )
                  & ( r1_lattices @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ X5 @ X7 )
      | ~ ( r1_lattices @ X6 @ X7 @ X5 )
      | ( X5 = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_lattices])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( r1_lattices @ sk_A @ X0 @ sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('79',plain,(
    ! [X1: $i] :
      ( ( l2_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('80',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( r1_lattices @ sk_A @ X0 @ sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['71','77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','81'])).

thf('83',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','85'])).

thf('87',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','91'])).

thf('93',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['0','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PRjT34m6NQ
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:50:07 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 80 iterations in 0.043s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.53  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.53  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.53  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.21/0.53  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.21/0.53  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.53  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.21/0.53  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.53  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.53  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.53  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.53  thf(t42_lattice3, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.53               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.53                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_k16_lattice3, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l3_lattices @ X8)
% 0.21/0.53          | (v2_struct_0 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k16_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.53  thf('2', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l3_lattices @ X8)
% 0.21/0.53          | (v2_struct_0 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k16_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.53  thf(t34_lattice3, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.21/0.53               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.21/0.53                 ( ![D:$i]:
% 0.21/0.53                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.21/0.53                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.21/0.53          | ((X10) != (k16_lattice3 @ X11 @ X12))
% 0.21/0.53          | ~ (r3_lattice3 @ X11 @ X13 @ X12)
% 0.21/0.53          | (r3_lattices @ X11 @ X13 @ X10)
% 0.21/0.53          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.21/0.53          | ~ (l3_lattices @ X11)
% 0.21/0.53          | ~ (v4_lattice3 @ X11)
% 0.21/0.53          | ~ (v10_lattices @ X11)
% 0.21/0.53          | (v2_struct_0 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X11)
% 0.21/0.53          | ~ (v10_lattices @ X11)
% 0.21/0.53          | ~ (v4_lattice3 @ X11)
% 0.21/0.53          | ~ (l3_lattices @ X11)
% 0.21/0.53          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.21/0.53          | (r3_lattices @ X11 @ X13 @ (k16_lattice3 @ X11 @ X12))
% 0.21/0.53          | ~ (r3_lattice3 @ X11 @ X13 @ X12)
% 0.21/0.53          | ~ (m1_subset_1 @ (k16_lattice3 @ X11 @ X12) @ (u1_struct_0 @ X11)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.21/0.53          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | ~ (v4_lattice3 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v10_lattices @ X0)
% 0.21/0.53          | ~ (v4_lattice3 @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.21/0.53          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.21/0.53          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.53          | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.53  thf('10', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.21/0.53          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.21/0.53  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '15'])).
% 0.21/0.53  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_r3_lattices, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.53         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.21/0.53          | ~ (l3_lattices @ X3)
% 0.21/0.53          | ~ (v9_lattices @ X3)
% 0.21/0.53          | ~ (v8_lattices @ X3)
% 0.21/0.53          | ~ (v6_lattices @ X3)
% 0.21/0.53          | (v2_struct_0 @ X3)
% 0.21/0.53          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.53          | (r1_lattices @ X3 @ X2 @ X4)
% 0.21/0.53          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.53          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v6_lattices @ sk_A)
% 0.21/0.53          | ~ (v8_lattices @ sk_A)
% 0.21/0.53          | ~ (v9_lattices @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf(cc1_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l3_lattices @ A ) =>
% 0.21/0.53       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.53         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.53           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.53           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v6_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain, ((v6_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v8_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain, ((v8_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v9_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain, ((v9_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.53  thf('38', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.53          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '25', '31', '37', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '39'])).
% 0.21/0.53  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (((r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.21/0.53        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf('43', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t38_lattice3, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( r2_hidden @ B @ C ) =>
% 0.21/0.53               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.21/0.53                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.53          | (r3_lattices @ X16 @ (k16_lattice3 @ X16 @ X17) @ X15)
% 0.21/0.53          | ~ (r2_hidden @ X15 @ X17)
% 0.21/0.53          | ~ (l3_lattices @ X16)
% 0.21/0.53          | ~ (v4_lattice3 @ X16)
% 0.21/0.53          | ~ (v10_lattices @ X16)
% 0.21/0.53          | (v2_struct_0 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v10_lattices @ sk_A)
% 0.21/0.53          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.53          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('48', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('49', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.53          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.21/0.53  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.53          | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '52'])).
% 0.21/0.53  thf('54', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l3_lattices @ X8)
% 0.21/0.53          | (v2_struct_0 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k16_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.21/0.53          | ~ (l3_lattices @ X3)
% 0.21/0.53          | ~ (v9_lattices @ X3)
% 0.21/0.53          | ~ (v8_lattices @ X3)
% 0.21/0.53          | ~ (v6_lattices @ X3)
% 0.21/0.53          | (v2_struct_0 @ X3)
% 0.21/0.53          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.53          | (r1_lattices @ X3 @ X2 @ X4)
% 0.21/0.53          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.53          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v6_lattices @ X0)
% 0.21/0.53          | ~ (v8_lattices @ X0)
% 0.21/0.53          | ~ (v9_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v9_lattices @ X0)
% 0.21/0.53          | ~ (v8_lattices @ X0)
% 0.21/0.53          | ~ (v6_lattices @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.53          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.53          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.53          | ~ (v6_lattices @ sk_A)
% 0.21/0.53          | ~ (v8_lattices @ sk_A)
% 0.21/0.53          | ~ (v9_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['54', '58'])).
% 0.21/0.53  thf('60', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('61', plain, ((v6_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.53  thf('62', plain, ((v8_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.53  thf('63', plain, ((v9_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.53          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.21/0.53  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.53          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.53      inference('clc', [status(thm)], ['64', '65'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '66'])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l3_lattices @ X8)
% 0.21/0.53          | (v2_struct_0 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k16_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.53  thf('69', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t26_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & ( l2_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ( ( r1_lattices @ A @ B @ C ) & ( r1_lattices @ A @ C @ B ) ) =>
% 0.21/0.53                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.21/0.53          | ~ (r1_lattices @ X6 @ X5 @ X7)
% 0.21/0.53          | ~ (r1_lattices @ X6 @ X7 @ X5)
% 0.21/0.53          | ((X5) = (X7))
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.21/0.53          | ~ (l2_lattices @ X6)
% 0.21/0.53          | ~ (v4_lattices @ X6)
% 0.21/0.53          | (v2_struct_0 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [t26_lattices])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v4_lattices @ sk_A)
% 0.21/0.53          | ~ (l2_lattices @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ((sk_B) = (X0))
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ X0 @ sk_B)
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v4_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.53  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('76', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('77', plain, ((v4_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.53  thf('78', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_l3_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.53  thf('79', plain, (![X1 : $i]: ((l2_lattices @ X1) | ~ (l3_lattices @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.53  thf('80', plain, ((l2_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ((sk_B) = (X0))
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ X0 @ sk_B)
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['71', '77', '80'])).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.53          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['68', '81'])).
% 0.21/0.53  thf('83', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.53          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.53          | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('simplify', [status(thm)], ['84'])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.21/0.53        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['67', '85'])).
% 0.21/0.53  thf('87', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.21/0.53  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.21/0.53      inference('clc', [status(thm)], ['88', '89'])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      (~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['42', '90'])).
% 0.21/0.53  thf('92', plain, (((v2_struct_0 @ sk_A) | ~ (l3_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '91'])).
% 0.21/0.53  thf('93', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('94', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['92', '93'])).
% 0.21/0.53  thf('95', plain, ($false), inference('demod', [status(thm)], ['0', '94'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
