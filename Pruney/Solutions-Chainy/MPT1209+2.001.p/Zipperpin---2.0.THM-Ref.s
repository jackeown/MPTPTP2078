%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oFUIvqs2eu

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 261 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          : 1020 (3026 expanded)
%              Number of equality atoms :   49 ( 137 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t44_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B )
            = ( k6_lattices @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v14_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B )
              = ( k6_lattices @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf(d8_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v8_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C )
                  = C ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v8_lattices @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k1_lattices @ X7 @ ( k2_lattices @ X7 @ X9 @ X8 ) @ X8 )
        = X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k2_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( v8_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v8_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ ( k2_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) )
    | ~ ( v8_lattices @ sk_A ) ),
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
    ! [X11: $i] :
      ( ( l2_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('9',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9','10','16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k4_lattices @ X16 @ X15 @ X17 )
        = ( k2_lattices @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( l1_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('30',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','27','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('36',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k4_lattices @ A @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( ( k4_lattices @ X5 @ X4 @ X6 )
        = ( k4_lattices @ X5 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('41',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B )
            = B ) ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( ( k4_lattices @ X19 @ ( k6_lattices @ X19 ) @ X18 )
        = X18 )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v14_lattices @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t43_lattices])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v14_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = sk_B_1 ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_B_1
    = ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','61'])).

thf('63',plain,(
    ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
 != ( k6_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('66',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','77'])).

thf('79',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
 != ( k6_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['63','82'])).

thf('84',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('86',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 )
      | ~ ( v4_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k3_lattices @ X13 @ X12 @ X14 )
        = ( k1_lattices @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('89',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
 != ( k6_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['83','97'])).

thf('99',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['62','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oFUIvqs2eu
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 81 iterations in 0.044s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.20/0.50  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.20/0.50  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.20/0.50  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.20/0.50  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.50  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.20/0.50  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.50  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.20/0.50  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.20/0.50  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.20/0.50  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.20/0.50  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(t44_lattices, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.50         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 0.20/0.50             ( k6_lattices @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.50            ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50              ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 0.20/0.50                ( k6_lattices @ A ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t44_lattices])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k6_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.50          | ~ (l2_lattices @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.50  thf(d8_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ( v8_lattices @ A ) <=>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50             ( ![C:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 0.20/0.50                   ( C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (v8_lattices @ X7)
% 0.20/0.50          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ((k1_lattices @ X7 @ (k2_lattices @ X7 @ X9 @ X8) @ X8) = (X8))
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l3_lattices @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_lattices])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l2_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ((k1_lattices @ X0 @ 
% 0.20/0.50              (k2_lattices @ X0 @ X1 @ (k6_lattices @ X0)) @ (k6_lattices @ X0))
% 0.20/0.50              = (k6_lattices @ X0))
% 0.20/0.50          | ~ (v8_lattices @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v8_lattices @ X0)
% 0.20/0.50          | ((k1_lattices @ X0 @ 
% 0.20/0.50              (k2_lattices @ X0 @ X1 @ (k6_lattices @ X0)) @ (k6_lattices @ X0))
% 0.20/0.50              = (k6_lattices @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | ~ (l2_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l2_lattices @ sk_A)
% 0.20/0.50        | ~ (l3_lattices @ sk_A)
% 0.20/0.50        | ((k1_lattices @ sk_A @ 
% 0.20/0.50            (k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) @ 
% 0.20/0.50            (k6_lattices @ sk_A)) = (k6_lattices @ sk_A))
% 0.20/0.50        | ~ (v8_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.50  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_l3_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.20/0.50  thf('8', plain, (![X11 : $i]: ((l2_lattices @ X11) | ~ (l3_lattices @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.50  thf('9', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l3_lattices @ A ) =>
% 0.20/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.20/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.50           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.20/0.50           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v8_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain, ((v8_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k1_lattices @ sk_A @ 
% 0.20/0.50            (k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) @ 
% 0.20/0.50            (k6_lattices @ sk_A)) = (k6_lattices @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '9', '10', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.50          | ~ (l2_lattices @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.50  thf('19', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k4_lattices, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.50         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.20/0.50          | ~ (l1_lattices @ X16)
% 0.20/0.50          | ~ (v6_lattices @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16)
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.20/0.50          | ((k4_lattices @ X16 @ X15 @ X17) = (k2_lattices @ X16 @ X15 @ X17)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50            = (k2_lattices @ sk_A @ sk_B_1 @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v6_lattices @ sk_A)
% 0.20/0.50          | ~ (l1_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v6_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain, ((v6_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.50  thf('28', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X11 : $i]: ((l1_lattices @ X11) | ~ (l3_lattices @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.50  thf('30', plain, ((l1_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50            = (k2_lattices @ sk_A @ sk_B_1 @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '27', '30'])).
% 0.20/0.50  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50              = (k2_lattices @ sk_A @ sk_B_1 @ X0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l2_lattices @ sk_A)
% 0.20/0.50        | ((k4_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50            = (k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '33'])).
% 0.20/0.50  thf('35', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.50          | ~ (l2_lattices @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.50  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(commutativity_k4_lattices, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.50         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (l1_lattices @ X5)
% 0.20/0.50          | ~ (v6_lattices @ X5)
% 0.20/0.50          | (v2_struct_0 @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ((k4_lattices @ X5 @ X4 @ X6) = (k4_lattices @ X5 @ X6 @ X4)))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50            = (k4_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v6_lattices @ sk_A)
% 0.20/0.50          | ~ (l1_lattices @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain, ((v6_lattices @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.51  thf('41', plain, ((l1_lattices @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.51            = (k4_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.51  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.51              = (k4_lattices @ sk_A @ X0 @ sk_B_1)))),
% 0.20/0.51      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l2_lattices @ sk_A)
% 0.20/0.51        | ((k4_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51            = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '44'])).
% 0.20/0.51  thf('46', plain, ((l2_lattices @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('47', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t43_lattices, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.51         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51           ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.20/0.51          | ((k4_lattices @ X19 @ (k6_lattices @ X19) @ X18) = (X18))
% 0.20/0.51          | ~ (l3_lattices @ X19)
% 0.20/0.51          | ~ (v14_lattices @ X19)
% 0.20/0.51          | ~ (v10_lattices @ X19)
% 0.20/0.51          | (v2_struct_0 @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [t43_lattices])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v10_lattices @ sk_A)
% 0.20/0.51        | ~ (v14_lattices @ sk_A)
% 0.20/0.51        | ~ (l3_lattices @ sk_A)
% 0.20/0.51        | ((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain, ((v10_lattices @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('51', plain, ((v14_lattices @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain, ((l3_lattices @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.20/0.51  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.20/0.51      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k4_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['45', '46', '55'])).
% 0.20/0.51  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (((k4_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1))),
% 0.20/0.51      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((sk_B_1) = (k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35', '58'])).
% 0.20/0.51  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (((sk_B_1) = (k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51            = (k6_lattices @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '61'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1)
% 0.20/0.51         != (k6_lattices @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.51          | ~ (l2_lattices @ X10)
% 0.20/0.51          | (v2_struct_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.51  thf('65', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(commutativity_k3_lattices, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.51         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.51          | ~ (l2_lattices @ X2)
% 0.20/0.51          | ~ (v4_lattices @ X2)
% 0.20/0.51          | (v2_struct_0 @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.51          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.51            = (k3_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v4_lattices @ sk_A)
% 0.20/0.51          | ~ (l2_lattices @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v10_lattices @ X0)
% 0.20/0.51          | (v4_lattices @ X0)
% 0.20/0.51          | ~ (l3_lattices @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.51  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain, ((l3_lattices @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain, ((v10_lattices @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain, ((v4_lattices @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.20/0.51  thf('74', plain, ((l2_lattices @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.51            = (k3_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['67', '73', '74'])).
% 0.20/0.51  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.51              = (k3_lattices @ sk_A @ X0 @ sk_B_1)))),
% 0.20/0.51      inference('clc', [status(thm)], ['75', '76'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l2_lattices @ sk_A)
% 0.20/0.51        | ((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51            = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['64', '77'])).
% 0.20/0.51  thf('79', plain, ((l2_lattices @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51            = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      (((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51         = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1))),
% 0.20/0.51      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51         != (k6_lattices @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['63', '82'])).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.51          | ~ (l2_lattices @ X10)
% 0.20/0.51          | (v2_struct_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.51  thf('85', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k3_lattices, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.51         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.51          | ~ (l2_lattices @ X13)
% 0.20/0.51          | ~ (v4_lattices @ X13)
% 0.20/0.51          | (v2_struct_0 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.51          | ((k3_lattices @ X13 @ X12 @ X14) = (k1_lattices @ X13 @ X12 @ X14)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.51            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v4_lattices @ sk_A)
% 0.20/0.51          | ~ (l2_lattices @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.51  thf('88', plain, ((v4_lattices @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.20/0.51  thf('89', plain, ((l2_lattices @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('90', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.51            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.20/0.51  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.51              = (k1_lattices @ sk_A @ sk_B_1 @ X0)))),
% 0.20/0.51      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l2_lattices @ sk_A)
% 0.20/0.51        | ((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51            = (k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['84', '92'])).
% 0.20/0.51  thf('94', plain, ((l2_lattices @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51            = (k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51         = (k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['95', '96'])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (((k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.51         != (k6_lattices @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['83', '97'])).
% 0.20/0.51  thf('99', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['62', '98'])).
% 0.20/0.51  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
