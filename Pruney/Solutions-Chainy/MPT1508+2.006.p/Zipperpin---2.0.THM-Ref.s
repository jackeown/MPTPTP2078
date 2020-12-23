%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.81IpQCwmR2

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 235 expanded)
%              Number of leaves         :   31 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  878 (3264 expanded)
%              Number of equality atoms :    9 (  99 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('1',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r3_lattices @ X11 @ ( k16_lattice3 @ X11 @ X12 ) @ X10 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v4_lattice3 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

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

thf('14',plain,(
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

thf('15',plain,(
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
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','24','30','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['11','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

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

thf('42',plain,(
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

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k16_lattice3 @ X0 @ X1 )
        = X2 )
      | ~ ( r1_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ( ( k16_lattice3 @ X0 @ X1 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k16_lattice3 @ sk_A @ sk_C )
      = sk_B )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('54',plain,(
    ! [X1: $i] :
      ( ( l2_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('55',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('58',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r3_lattice3 @ A @ B @ C )
             => ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r3_lattices @ X14 @ X13 @ ( k16_lattice3 @ X14 @ X15 ) )
      | ~ ( r3_lattice3 @ X14 @ X13 @ X15 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice3])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('73',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('74',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','79'])).

thf('81',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k16_lattice3 @ sk_A @ sk_C )
      = sk_B ) ),
    inference(demod,[status(thm)],['45','46','52','55','56','84'])).

thf('86',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.81IpQCwmR2
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 56 iterations in 0.033s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.20/0.48  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.20/0.48  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.20/0.48  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.20/0.48  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.20/0.48  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.20/0.48  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.20/0.48  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.20/0.48  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.20/0.48  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.20/0.48  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.20/0.48  thf(t42_lattice3, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.20/0.48               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.20/0.48                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.20/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
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
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.48          | (r3_lattices @ X11 @ (k16_lattice3 @ X11 @ X12) @ X10)
% 0.20/0.48          | ~ (r2_hidden @ X10 @ X12)
% 0.20/0.48          | ~ (l3_lattices @ X11)
% 0.20/0.48          | ~ (v4_lattice3 @ X11)
% 0.20/0.48          | ~ (v10_lattices @ X11)
% 0.20/0.48          | (v2_struct_0 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v10_lattices @ sk_A)
% 0.20/0.48          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.48          | ~ (l3_lattices @ sk_A)
% 0.20/0.48          | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.48          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.48          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.20/0.48  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.48          | ~ (r2_hidden @ sk_B @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '10'])).
% 0.20/0.48  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k16_lattice3, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (l3_lattices @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8)
% 0.20/0.48          | (m1_subset_1 @ (k16_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.20/0.48  thf(redefinition_r3_lattices, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.48         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.20/0.48          | ~ (l3_lattices @ X3)
% 0.20/0.48          | ~ (v9_lattices @ X3)
% 0.20/0.48          | ~ (v8_lattices @ X3)
% 0.20/0.48          | ~ (v6_lattices @ X3)
% 0.20/0.48          | (v2_struct_0 @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.48          | (r1_lattices @ X3 @ X2 @ X4)
% 0.20/0.48          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.48          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v6_lattices @ X0)
% 0.20/0.48          | ~ (v8_lattices @ X0)
% 0.20/0.48          | ~ (v9_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (v9_lattices @ X0)
% 0.20/0.48          | ~ (v8_lattices @ X0)
% 0.20/0.48          | ~ (v6_lattices @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.48          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l3_lattices @ sk_A)
% 0.20/0.48          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.48          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.48          | ~ (v6_lattices @ sk_A)
% 0.20/0.48          | ~ (v8_lattices @ sk_A)
% 0.20/0.48          | ~ (v9_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '16'])).
% 0.20/0.48  thf('18', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l3_lattices @ A ) =>
% 0.20/0.48       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.20/0.48         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.48           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.20/0.48           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v6_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.48  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain, ((v6_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v8_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.48  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, ((v8_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v9_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.48  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain, ((v9_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.48          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18', '24', '30', '36'])).
% 0.20/0.48  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.48          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (l3_lattices @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8)
% 0.20/0.48          | (m1_subset_1 @ (k16_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.20/0.48  thf(t26_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & ( l2_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48               ( ( ( r1_lattices @ A @ B @ C ) & ( r1_lattices @ A @ C @ B ) ) =>
% 0.20/0.48                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('42', plain,
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
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v4_lattices @ X0)
% 0.20/0.48          | ~ (l2_lattices @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ((k16_lattice3 @ X0 @ X1) = (X2))
% 0.20/0.48          | ~ (r1_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.20/0.48          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.48          | ~ (r1_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.20/0.48          | ((k16_lattice3 @ X0 @ X1) = (X2))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l2_lattices @ X0)
% 0.20/0.48          | ~ (v4_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l3_lattices @ sk_A)
% 0.20/0.48        | ~ (v4_lattices @ sk_A)
% 0.20/0.48        | ~ (l2_lattices @ sk_A)
% 0.20/0.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | ((k16_lattice3 @ sk_A @ sk_C) = (sk_B))
% 0.20/0.48        | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '44'])).
% 0.20/0.48  thf('46', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v4_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.48  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain, ((v4_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.48  thf('53', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_l3_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.20/0.48  thf('54', plain, (![X1 : $i]: ((l2_lattices @ X1) | ~ (l3_lattices @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.48  thf('55', plain, ((l2_lattices @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('56', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (l3_lattices @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8)
% 0.20/0.48          | (m1_subset_1 @ (k16_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.20/0.48  thf('58', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t40_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.20/0.48               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.20/0.48          | (r3_lattices @ X14 @ X13 @ (k16_lattice3 @ X14 @ X15))
% 0.20/0.48          | ~ (r3_lattice3 @ X14 @ X13 @ X15)
% 0.20/0.48          | ~ (l3_lattices @ X14)
% 0.20/0.48          | ~ (v4_lattice3 @ X14)
% 0.20/0.48          | ~ (v10_lattices @ X14)
% 0.20/0.48          | (v2_struct_0 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t40_lattice3])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v10_lattices @ sk_A)
% 0.20/0.48          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.48          | ~ (l3_lattices @ sk_A)
% 0.20/0.48          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('62', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('63', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('64', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.20/0.48  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.20/0.48          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['58', '67'])).
% 0.20/0.48  thf('69', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.20/0.48          | ~ (l3_lattices @ X3)
% 0.20/0.48          | ~ (v9_lattices @ X3)
% 0.20/0.48          | ~ (v8_lattices @ X3)
% 0.20/0.48          | ~ (v6_lattices @ X3)
% 0.20/0.48          | (v2_struct_0 @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.48          | (r1_lattices @ X3 @ X2 @ X4)
% 0.20/0.48          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v6_lattices @ sk_A)
% 0.20/0.48          | ~ (v8_lattices @ sk_A)
% 0.20/0.48          | ~ (v9_lattices @ sk_A)
% 0.20/0.48          | ~ (l3_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.48  thf('72', plain, ((v6_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.48  thf('73', plain, ((v8_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.48  thf('74', plain, ((v9_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.48  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('76', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 0.20/0.48  thf('77', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['68', '76'])).
% 0.20/0.48  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      (((r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.20/0.48        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['77', '78'])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l3_lattices @ sk_A)
% 0.20/0.48        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['57', '79'])).
% 0.20/0.48  thf('81', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.48  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('84', plain,
% 0.20/0.48      ((r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['82', '83'])).
% 0.20/0.48  thf('85', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A) | ((k16_lattice3 @ sk_A @ sk_C) = (sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '46', '52', '55', '56', '84'])).
% 0.20/0.48  thf('86', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('87', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.20/0.48  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
