%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sxljygmcdS

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 280 expanded)
%              Number of leaves         :   30 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          : 1135 (4656 expanded)
%              Number of equality atoms :   42 (  49 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t53_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_lattices @ A @ B @ C )
               => ( r3_lattices @ A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v17_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r3_lattices @ A @ B @ C )
                 => ( r3_lattices @ A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_lattices])).

thf('0',plain,(
    ~ ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_lattices,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) )
                = ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( ( k7_lattices @ X10 @ ( k3_lattices @ X10 @ X9 @ X11 ) )
        = ( k4_lattices @ X10 @ ( k7_lattices @ X10 @ X9 ) @ ( k7_lattices @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v17_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t51_lattices])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_B ) ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( ( k7_lattices @ X10 @ ( k3_lattices @ X10 @ X9 @ X11 ) )
        = ( k4_lattices @ X10 @ ( k7_lattices @ X10 @ X9 ) @ ( k7_lattices @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v17_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t51_lattices])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) )
            = B ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( ( k7_lattices @ X8 @ ( k7_lattices @ X8 @ X7 ) )
        = X7 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v17_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_lattices])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) )
    = sk_B ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
        = ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
        = ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_C ) )
    = ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k3_lattices @ A @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

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

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('49',plain,(
    ! [X6: $i] :
      ( ( l2_lattices @ X6 )
      | ~ ( l3_lattices @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('50',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','47','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_B ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('55',plain,
    ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_B ) ) )
    = ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( ( k7_lattices @ X8 @ ( k7_lattices @ X8 @ X7 ) )
        = X7 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v17_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_lattices])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) )
    = sk_C ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( k4_lattices @ A @ B @ C )
                  = ( k5_lattices @ A ) )
              <=> ( r3_lattices @ A @ B @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r3_lattices @ X13 @ X12 @ ( k7_lattices @ X13 @ X14 ) )
      | ( ( k4_lattices @ X13 @ X12 @ X14 )
        = ( k5_lattices @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v17_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_lattices])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k5_lattices @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k5_lattices @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ sk_C )
    | ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
      = ( k5_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    r3_lattices @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
      = ( k5_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_B ) ) )
    = ( k5_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['55','83'])).

thf('85',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) )
    = sk_B ),
    inference(clc,[status(thm)],['31','32'])).

thf('86',plain,
    ( ( k5_lattices @ sk_A )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('88',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattices @ X13 @ X12 @ X14 )
       != ( k5_lattices @ X13 ) )
      | ( r3_lattices @ X13 @ X12 @ ( k7_lattices @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v17_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_lattices])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
       != ( k5_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
       != ( k5_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sxljygmcdS
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:52:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 133 iterations in 0.060s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.52  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.52  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.21/0.52  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.52  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.21/0.52  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.52  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 0.21/0.52  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.52  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.52  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.52  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.52  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(t53_lattices, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.52         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52               ( ( r3_lattices @ A @ B @ C ) =>
% 0.21/0.52                 ( r3_lattices @
% 0.21/0.52                   A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.52            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                  ( ( r3_lattices @ A @ B @ C ) =>
% 0.21/0.52                    ( r3_lattices @
% 0.21/0.52                      A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t53_lattices])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52          (k7_lattices @ sk_A @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k7_lattices, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (l3_lattices @ X4)
% 0.21/0.52          | (v2_struct_0 @ X4)
% 0.21/0.52          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.52          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (l3_lattices @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t51_lattices, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.52         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52               ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) ) =
% 0.21/0.52                 ( k4_lattices @
% 0.21/0.52                   A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.52          | ((k7_lattices @ X10 @ (k3_lattices @ X10 @ X9 @ X11))
% 0.21/0.52              = (k4_lattices @ X10 @ (k7_lattices @ X10 @ X9) @ 
% 0.21/0.52                 (k7_lattices @ X10 @ X11)))
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.52          | ~ (l3_lattices @ X10)
% 0.21/0.52          | ~ (v17_lattices @ X10)
% 0.21/0.52          | ~ (v10_lattices @ X10)
% 0.21/0.52          | (v2_struct_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t51_lattices])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v10_lattices @ sk_A)
% 0.21/0.52          | ~ (v17_lattices @ sk_A)
% 0.21/0.52          | ~ (l3_lattices @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C @ X0))
% 0.21/0.52              = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52                 (k7_lattices @ sk_A @ X0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain, ((v10_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain, ((v17_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('13', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C @ X0))
% 0.21/0.52              = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52                 (k7_lattices @ sk_A @ X0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.52  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C @ X0))
% 0.21/0.52            = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52               (k7_lattices @ sk_A @ X0)))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((k7_lattices @ sk_A @ 
% 0.21/0.52         (k3_lattices @ sk_A @ sk_C @ (k7_lattices @ sk_A @ sk_B)))
% 0.21/0.52         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '16'])).
% 0.21/0.52  thf('18', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.52          | ((k7_lattices @ X10 @ (k3_lattices @ X10 @ X9 @ X11))
% 0.21/0.52              = (k4_lattices @ X10 @ (k7_lattices @ X10 @ X9) @ 
% 0.21/0.52                 (k7_lattices @ X10 @ X11)))
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.52          | ~ (l3_lattices @ X10)
% 0.21/0.52          | ~ (v17_lattices @ X10)
% 0.21/0.52          | ~ (v10_lattices @ X10)
% 0.21/0.52          | (v2_struct_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t51_lattices])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v10_lattices @ sk_A)
% 0.21/0.52          | ~ (v17_lattices @ sk_A)
% 0.21/0.52          | ~ (l3_lattices @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ((k7_lattices @ sk_A @ 
% 0.21/0.52              (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 0.21/0.52              = (k4_lattices @ sk_A @ 
% 0.21/0.52                 (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) @ 
% 0.21/0.52                 (k7_lattices @ sk_A @ X0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain, ((v10_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain, ((v17_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t49_lattices, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.52         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.52          | ((k7_lattices @ X8 @ (k7_lattices @ X8 @ X7)) = (X7))
% 0.21/0.52          | ~ (l3_lattices @ X8)
% 0.21/0.52          | ~ (v17_lattices @ X8)
% 0.21/0.52          | ~ (v10_lattices @ X8)
% 0.21/0.52          | (v2_struct_0 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t49_lattices])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v10_lattices @ sk_A)
% 0.21/0.52        | ~ (v17_lattices @ sk_A)
% 0.21/0.52        | ~ (l3_lattices @ sk_A)
% 0.21/0.52        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) = (sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain, ((v10_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain, ((v17_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) = (sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.52  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ((k7_lattices @ sk_A @ 
% 0.21/0.52              (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 0.21/0.52              = (k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ X0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22', '23', '24', '33'])).
% 0.21/0.52  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k7_lattices @ sk_A @ 
% 0.21/0.52            (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 0.21/0.52            = (k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ X0)))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (((k7_lattices @ sk_A @ 
% 0.21/0.52         (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_C))
% 0.21/0.52         = (k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('39', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(commutativity_k3_lattices, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.52         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.52          | ~ (l2_lattices @ X2)
% 0.21/0.52          | ~ (v4_lattices @ X2)
% 0.21/0.52          | (v2_struct_0 @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.52          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_lattices @ sk_A @ sk_C @ X0) = (k3_lattices @ sk_A @ X0 @ sk_C))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v4_lattices @ sk_A)
% 0.21/0.52          | ~ (l2_lattices @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf(cc1_lattices, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l3_lattices @ A ) =>
% 0.21/0.52       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.52         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.52           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.52           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v10_lattices @ X0)
% 0.21/0.52          | (v4_lattices @ X0)
% 0.21/0.52          | ~ (l3_lattices @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.52  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain, ((v10_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain, ((v4_lattices @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.52  thf('48', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_l3_lattices, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.52  thf('49', plain, (![X6 : $i]: ((l2_lattices @ X6) | ~ (l3_lattices @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.52  thf('50', plain, ((l2_lattices @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_lattices @ sk_A @ sk_C @ X0) = (k3_lattices @ sk_A @ X0 @ sk_C))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '47', '50'])).
% 0.21/0.52  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ((k3_lattices @ sk_A @ sk_C @ X0)
% 0.21/0.52              = (k3_lattices @ sk_A @ X0 @ sk_C)))),
% 0.21/0.52      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((k3_lattices @ sk_A @ sk_C @ (k7_lattices @ sk_A @ sk_B))
% 0.21/0.52         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (((k7_lattices @ sk_A @ 
% 0.21/0.52         (k3_lattices @ sk_A @ sk_C @ (k7_lattices @ sk_A @ sk_B)))
% 0.21/0.52         = (k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['37', '54'])).
% 0.21/0.52  thf('56', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.52          | ((k7_lattices @ X8 @ (k7_lattices @ X8 @ X7)) = (X7))
% 0.21/0.52          | ~ (l3_lattices @ X8)
% 0.21/0.52          | ~ (v17_lattices @ X8)
% 0.21/0.52          | ~ (v10_lattices @ X8)
% 0.21/0.52          | (v2_struct_0 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t49_lattices])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v10_lattices @ sk_A)
% 0.21/0.52        | ~ (v17_lattices @ sk_A)
% 0.21/0.52        | ~ (l3_lattices @ sk_A)
% 0.21/0.52        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.52  thf('59', plain, ((v10_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('60', plain, ((v17_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.21/0.52  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C))),
% 0.21/0.52      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('65', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t52_lattices, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.52         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52               ( ( ( k4_lattices @ A @ B @ C ) = ( k5_lattices @ A ) ) <=>
% 0.21/0.52                 ( r3_lattices @ A @ B @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.52          | ~ (r3_lattices @ X13 @ X12 @ (k7_lattices @ X13 @ X14))
% 0.21/0.52          | ((k4_lattices @ X13 @ X12 @ X14) = (k5_lattices @ X13))
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.52          | ~ (l3_lattices @ X13)
% 0.21/0.52          | ~ (v17_lattices @ X13)
% 0.21/0.52          | ~ (v10_lattices @ X13)
% 0.21/0.52          | (v2_struct_0 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t52_lattices])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v10_lattices @ sk_A)
% 0.21/0.52          | ~ (v17_lattices @ sk_A)
% 0.21/0.52          | ~ (l3_lattices @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ((k4_lattices @ sk_A @ sk_B @ X0) = (k5_lattices @ sk_A))
% 0.21/0.52          | ~ (r3_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.52  thf('68', plain, ((v10_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('69', plain, ((v17_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ((k4_lattices @ sk_A @ sk_B @ X0) = (k5_lattices @ sk_A))
% 0.21/0.52          | ~ (r3_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      ((~ (r3_lattices @ sk_A @ sk_B @ sk_C)
% 0.21/0.52        | ((k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C))
% 0.21/0.52            = (k5_lattices @ sk_A))
% 0.21/0.52        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '71'])).
% 0.21/0.52  thf('73', plain, ((r3_lattices @ sk_A @ sk_B @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (l3_lattices @ X4)
% 0.21/0.52          | (v2_struct_0 @ X4)
% 0.21/0.52          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.52          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (l3_lattices @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.52  thf('77', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      ((((k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C))
% 0.21/0.52          = (k5_lattices @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['72', '73', '80'])).
% 0.21/0.52  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (((k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C))
% 0.21/0.52         = (k5_lattices @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      (((k7_lattices @ sk_A @ 
% 0.21/0.52         (k3_lattices @ sk_A @ sk_C @ (k7_lattices @ sk_A @ sk_B)))
% 0.21/0.52         = (k5_lattices @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['55', '83'])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (((k5_lattices @ sk_A)
% 0.21/0.52         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '84', '85'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.52          | ((k4_lattices @ X13 @ X12 @ X14) != (k5_lattices @ X13))
% 0.21/0.52          | (r3_lattices @ X13 @ X12 @ (k7_lattices @ X13 @ X14))
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.52          | ~ (l3_lattices @ X13)
% 0.21/0.52          | ~ (v17_lattices @ X13)
% 0.21/0.52          | ~ (v10_lattices @ X13)
% 0.21/0.52          | (v2_struct_0 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t52_lattices])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v10_lattices @ sk_A)
% 0.21/0.52          | ~ (v17_lattices @ sk_A)
% 0.21/0.52          | ~ (l3_lattices @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52             (k7_lattices @ sk_A @ X0))
% 0.21/0.52          | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.21/0.52              != (k5_lattices @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.52  thf('90', plain, ((v10_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('91', plain, ((v17_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('92', plain, ((l3_lattices @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52             (k7_lattices @ sk_A @ X0))
% 0.21/0.52          | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.21/0.52              != (k5_lattices @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      ((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 0.21/0.52        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52           (k7_lattices @ sk_A @ sk_B))
% 0.21/0.52        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['86', '93'])).
% 0.21/0.52  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      ((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 0.21/0.52        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52           (k7_lattices @ sk_A @ sk_B))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52           (k7_lattices @ sk_A @ sk_B)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['96'])).
% 0.21/0.52  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('99', plain,
% 0.21/0.52      ((r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.52        (k7_lattices @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['97', '98'])).
% 0.21/0.52  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
