%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1507+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eyMXtIdoYA

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 182 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  830 (2494 expanded)
%              Number of equality atoms :   11 (  77 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(t41_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( r2_hidden @ B @ C )
                & ( r4_lattice3 @ A @ B @ C ) )
             => ( ( k15_lattice3 @ A @ C )
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
                  & ( r4_lattice3 @ A @ B @ C ) )
               => ( ( k15_lattice3 @ A @ C )
                  = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r4_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
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

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( X2
       != ( k15_lattice3 @ X1 @ X3 ) )
      | ~ ( r4_lattice3 @ X1 @ X4 @ X3 )
      | ( r1_lattices @ X1 @ X2 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('5',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X3 ) @ X4 )
      | ~ ( r4_lattice3 @ X1 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
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
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_lattices @ X12 @ X11 @ X13 )
      | ~ ( r1_lattices @ X12 @ X13 @ X11 )
      | ( X11 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l2_lattices @ X12 )
      | ~ ( v4_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t26_lattices])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = X2 )
      | ~ ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k15_lattice3 @ sk_A @ sk_C )
      = sk_B )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( ( l2_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('30',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('33',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( r3_lattices @ X15 @ X14 @ ( k15_lattice3 @ X15 @ X16 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v9_lattices @ X9 )
      | ~ ( v8_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r1_lattices @ X9 @ X8 @ X10 )
      | ~ ( r3_lattices @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','52','58','64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','69'])).

thf('71',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_C )
      = sk_B ) ),
    inference(demod,[status(thm)],['20','21','27','30','31','74'])).

thf('76',plain,(
    ( k15_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).


%------------------------------------------------------------------------------
