%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zBg5L1kjBH

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:30 EST 2020

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

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

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ~ ( v4_lattice3 @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( X9
       != ( k15_lattice3 @ X8 @ X10 ) )
      | ~ ( r4_lattice3 @ X8 @ X11 @ X10 )
      | ( r1_lattices @ X8 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('5',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ( r1_lattices @ X8 @ ( k15_lattice3 @ X8 @ X10 ) @ X11 )
      | ~ ( r4_lattice3 @ X8 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X8 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v4_lattice3 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
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
    ! [X1: $i] :
      ( ( l2_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('30',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zBg5L1kjBH
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:08:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 60 iterations in 0.036s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.20/0.48  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.20/0.48  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.48  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.20/0.48  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.20/0.48  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.20/0.48  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.20/0.48  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.20/0.48  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.20/0.48  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.20/0.48  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.20/0.48  thf(t41_lattice3, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.20/0.48               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.20/0.48                  ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t41_lattice3])).
% 0.20/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((r4_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k15_lattice3, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (l3_lattices @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12)
% 0.20/0.48          | (m1_subset_1 @ (k15_lattice3 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.20/0.48  thf(d21_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48         ( ![B:$i,C:$i]:
% 0.20/0.48           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.20/0.48               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.20/0.48                 ( ![D:$i]:
% 0.20/0.48                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.20/0.48                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X8)
% 0.20/0.48          | ~ (v10_lattices @ X8)
% 0.20/0.48          | ~ (v4_lattice3 @ X8)
% 0.20/0.48          | ~ (l3_lattices @ X8)
% 0.20/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ((X9) != (k15_lattice3 @ X8 @ X10))
% 0.20/0.48          | ~ (r4_lattice3 @ X8 @ X11 @ X10)
% 0.20/0.48          | (r1_lattices @ X8 @ X9 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ~ (l3_lattices @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.48          | (r1_lattices @ X8 @ (k15_lattice3 @ X8 @ X10) @ X11)
% 0.20/0.48          | ~ (r4_lattice3 @ X8 @ X11 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ (k15_lattice3 @ X8 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.48          | ~ (l3_lattices @ X8)
% 0.20/0.48          | ~ (v4_lattice3 @ X8)
% 0.20/0.48          | ~ (v10_lattices @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | ~ (v4_lattice3 @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.20/0.48          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.48          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.20/0.48          | ~ (v4_lattice3 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l3_lattices @ sk_A)
% 0.20/0.48          | ~ (v10_lattices @ sk_A)
% 0.20/0.48          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.48          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.48  thf('9', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.20/0.48  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.48          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (l3_lattices @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12)
% 0.20/0.48          | (m1_subset_1 @ (k15_lattice3 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.20/0.48  thf(t26_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & ( l2_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48               ( ( ( r1_lattices @ A @ B @ C ) & ( r1_lattices @ A @ C @ B ) ) =>
% 0.20/0.48                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.20/0.48          | ~ (r1_lattices @ X6 @ X5 @ X7)
% 0.20/0.48          | ~ (r1_lattices @ X6 @ X7 @ X5)
% 0.20/0.48          | ((X5) = (X7))
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.20/0.48          | ~ (l2_lattices @ X6)
% 0.20/0.48          | ~ (v4_lattices @ X6)
% 0.20/0.48          | (v2_struct_0 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_lattices])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v4_lattices @ X0)
% 0.20/0.48          | ~ (l2_lattices @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ((k15_lattice3 @ X0 @ X1) = (X2))
% 0.20/0.48          | ~ (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.20/0.48          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.48          | ~ (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.20/0.48          | ((k15_lattice3 @ X0 @ X1) = (X2))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l2_lattices @ X0)
% 0.20/0.48          | ~ (v4_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l3_lattices @ sk_A)
% 0.20/0.48        | ~ (v4_lattices @ sk_A)
% 0.20/0.48        | ~ (l2_lattices @ sk_A)
% 0.20/0.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | ((k15_lattice3 @ sk_A @ sk_C) = (sk_B))
% 0.20/0.48        | ~ (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '19'])).
% 0.20/0.48  thf('21', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l3_lattices @ A ) =>
% 0.20/0.48       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.20/0.48         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.48           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.20/0.48           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v4_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.48  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain, ((v4_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.48  thf('28', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_l3_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.20/0.48  thf('29', plain, (![X1 : $i]: ((l2_lattices @ X1) | ~ (l3_lattices @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.48  thf('30', plain, ((l2_lattices @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (l3_lattices @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12)
% 0.20/0.48          | (m1_subset_1 @ (k15_lattice3 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.20/0.48  thf('33', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t38_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( r2_hidden @ B @ C ) =>
% 0.20/0.48               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.20/0.48                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.48          | (r3_lattices @ X15 @ X14 @ (k15_lattice3 @ X15 @ X16))
% 0.20/0.48          | ~ (r2_hidden @ X14 @ X16)
% 0.20/0.48          | ~ (l3_lattices @ X15)
% 0.20/0.48          | ~ (v4_lattice3 @ X15)
% 0.20/0.48          | ~ (v10_lattices @ X15)
% 0.20/0.48          | (v2_struct_0 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v10_lattices @ sk_A)
% 0.20/0.48          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.48          | ~ (l3_lattices @ sk_A)
% 0.20/0.48          | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.48          | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.48          | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.20/0.48  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.20/0.48          | ~ (r2_hidden @ sk_B @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '42'])).
% 0.20/0.48  thf('44', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_r3_lattices, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.49         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.20/0.49          | ~ (l3_lattices @ X3)
% 0.20/0.49          | ~ (v9_lattices @ X3)
% 0.20/0.49          | ~ (v8_lattices @ X3)
% 0.20/0.49          | ~ (v6_lattices @ X3)
% 0.20/0.49          | (v2_struct_0 @ X3)
% 0.20/0.49          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.49          | (r1_lattices @ X3 @ X2 @ X4)
% 0.20/0.49          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v6_lattices @ sk_A)
% 0.20/0.49          | ~ (v8_lattices @ sk_A)
% 0.20/0.49          | ~ (v9_lattices @ sk_A)
% 0.20/0.49          | ~ (l3_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v10_lattices @ X0)
% 0.20/0.49          | (v6_lattices @ X0)
% 0.20/0.49          | ~ (l3_lattices @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.49  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain, ((v6_lattices @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v10_lattices @ X0)
% 0.20/0.49          | (v8_lattices @ X0)
% 0.20/0.49          | ~ (l3_lattices @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.49  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain, ((v8_lattices @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v10_lattices @ X0)
% 0.20/0.49          | (v9_lattices @ X0)
% 0.20/0.49          | ~ (l3_lattices @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.49  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('63', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('64', plain, ((v9_lattices @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.20/0.49  thf('65', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '52', '58', '64', '65'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '66'])).
% 0.20/0.49  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (((r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.20/0.49        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['67', '68'])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l3_lattices @ sk_A)
% 0.20/0.49        | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '69'])).
% 0.20/0.49  thf('71', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.49  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      ((r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['72', '73'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A) | ((k15_lattice3 @ sk_A @ sk_C) = (sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '27', '30', '31', '74'])).
% 0.20/0.49  thf('76', plain, (((k15_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.20/0.49  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
