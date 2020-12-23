%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RUZnit2fTI

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 176 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  712 (1818 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(t41_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v13_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_lattices])).

thf('0',plain,(
    ~ ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ~ ( v6_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r3_lattices @ X10 @ X9 @ X11 )
      | ~ ( r1_lattices @ X10 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( r3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( l1_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('9',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(d3_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k1_lattices @ A @ B @ C )
                  = C ) ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
       != X3 )
      | ( r1_lattices @ X2 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != X1 )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
     != sk_B ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( l2_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('19',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ~ ( v4_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k3_lattices @ X7 @ X6 @ X8 )
        = ( k1_lattices @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B )
            = B ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k3_lattices @ X13 @ ( k5_lattices @ X13 ) @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v13_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_lattices])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = sk_B ),
    inference(clc,[status(thm)],['33','34'])).

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

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','35','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( sk_B
    = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['15','16','19','45'])).

thf('47',plain,
    ( ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','9','49','55','61','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RUZnit2fTI
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:18:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 57 iterations in 0.048s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.50  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.50  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.50  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.50  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.50  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.50  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.21/0.50  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.50  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.50  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.50  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.50  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.50  thf(t41_lattices, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.50         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.50            ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50              ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t41_lattices])).
% 0.21/0.50  thf('0', plain, (~ (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k5_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X4 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.50          | ~ (l1_lattices @ X4)
% 0.21/0.50          | (v2_struct_0 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.50  thf(redefinition_r3_lattices, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.50         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.50          | ~ (l3_lattices @ X10)
% 0.21/0.50          | ~ (v9_lattices @ X10)
% 0.21/0.50          | ~ (v8_lattices @ X10)
% 0.21/0.50          | ~ (v6_lattices @ X10)
% 0.21/0.50          | (v2_struct_0 @ X10)
% 0.21/0.50          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.50          | (r3_lattices @ X10 @ X9 @ X11)
% 0.21/0.50          | ~ (r1_lattices @ X10 @ X9 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l1_lattices @ X0)
% 0.21/0.50          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.50          | (r3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v6_lattices @ X0)
% 0.21/0.50          | ~ (v8_lattices @ X0)
% 0.21/0.50          | ~ (v9_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (l3_lattices @ X0)
% 0.21/0.50          | ~ (v9_lattices @ X0)
% 0.21/0.50          | ~ (v8_lattices @ X0)
% 0.21/0.50          | ~ (v6_lattices @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (r3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.50          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.50          | ~ (l1_lattices @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_lattices @ sk_A)
% 0.21/0.50        | ~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.50        | (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.50        | ~ (v6_lattices @ sk_A)
% 0.21/0.50        | ~ (v8_lattices @ sk_A)
% 0.21/0.50        | ~ (v9_lattices @ sk_A)
% 0.21/0.50        | ~ (l3_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '5'])).
% 0.21/0.50  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l3_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.50  thf('8', plain, (![X5 : $i]: ((l1_lattices @ X5) | ~ (l3_lattices @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.50  thf('9', plain, ((l1_lattices @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X4 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.50          | ~ (l1_lattices @ X4)
% 0.21/0.50          | (v2_struct_0 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.50  thf(d3_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.50                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.50          | ((k1_lattices @ X2 @ X1 @ X3) != (X3))
% 0.21/0.50          | (r1_lattices @ X2 @ X1 @ X3)
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.50          | ~ (l2_lattices @ X2)
% 0.21/0.50          | (v2_struct_0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l1_lattices @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l2_lattices @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.50          | ((k1_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k1_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (X1))
% 0.21/0.50          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (l2_lattices @ X0)
% 0.21/0.50          | ~ (l1_lattices @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_lattices @ sk_A)
% 0.21/0.50        | ~ (l2_lattices @ sk_A)
% 0.21/0.50        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.50        | ((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) != (sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.50  thf('16', plain, ((l1_lattices @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('17', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain, (![X5 : $i]: ((l2_lattices @ X5) | ~ (l3_lattices @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.50  thf('19', plain, ((l2_lattices @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X4 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.50          | ~ (l1_lattices @ X4)
% 0.21/0.50          | (v2_struct_0 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.50  thf(redefinition_k3_lattices, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.50         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.21/0.50          | ~ (l2_lattices @ X7)
% 0.21/0.50          | ~ (v4_lattices @ X7)
% 0.21/0.50          | (v2_struct_0 @ X7)
% 0.21/0.50          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.50          | ((k3_lattices @ X7 @ X6 @ X8) = (k1_lattices @ X7 @ X6 @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l1_lattices @ X0)
% 0.21/0.50          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.50              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v4_lattices @ X0)
% 0.21/0.50          | ~ (l2_lattices @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (l2_lattices @ X0)
% 0.21/0.50          | ~ (v4_lattices @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.50              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.50          | ~ (l1_lattices @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_lattices @ sk_A)
% 0.21/0.50        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.50            = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 0.21/0.50        | ~ (v4_lattices @ sk_A)
% 0.21/0.50        | ~ (l2_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '24'])).
% 0.21/0.50  thf('26', plain, ((l1_lattices @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t39_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.50         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ((k3_lattices @ X13 @ (k5_lattices @ X13) @ X12) = (X12))
% 0.21/0.50          | ~ (l3_lattices @ X13)
% 0.21/0.50          | ~ (v13_lattices @ X13)
% 0.21/0.50          | ~ (v10_lattices @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t39_lattices])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v10_lattices @ sk_A)
% 0.21/0.50        | ~ (v13_lattices @ sk_A)
% 0.21/0.50        | ~ (l3_lattices @ sk_A)
% 0.21/0.50        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain, ((v13_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('32', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.21/0.50  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf(cc1_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l3_lattices @ A ) =>
% 0.21/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.50           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.50           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v4_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain, ((v4_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.50  thf('42', plain, ((l2_lattices @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ((sk_B) = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26', '35', '41', '42'])).
% 0.21/0.50  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (((sk_B) = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.50        | ((sk_B) != (sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16', '19', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.50  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain, ((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)),
% 0.21/0.50      inference('clc', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v6_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, ((v6_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v8_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('61', plain, ((v8_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v9_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('67', plain, ((v9_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.50  thf('68', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['6', '9', '49', '55', '61', '67', '68'])).
% 0.21/0.50  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('71', plain, ((r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)),
% 0.21/0.50      inference('clc', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
