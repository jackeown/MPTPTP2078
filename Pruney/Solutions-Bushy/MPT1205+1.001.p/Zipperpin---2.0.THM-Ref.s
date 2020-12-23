%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1205+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mdYGAY3yc0

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:15 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 131 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  604 (1394 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t39_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v13_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ~ ( v4_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k3_lattices @ X10 @ X9 @ X11 )
        = ( k1_lattices @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
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
    ! [X8: $i] :
      ( ( l1_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('9',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v8_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k1_lattices @ X4 @ ( k2_lattices @ X4 @ X6 @ X5 ) @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(d16_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v13_lattices @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( B
                = ( k5_lattices @ A ) )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( ( k2_lattices @ A @ B @ C )
                      = B )
                    & ( ( k2_lattices @ A @ C @ B )
                      = B ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v13_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( X2
       != ( k5_lattices @ X1 ) )
      | ( ( k2_lattices @ X1 @ X2 @ X3 )
        = X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ ( k5_lattices @ X1 ) @ X3 )
        = ( k5_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v13_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('35',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['39','40'])).

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

thf('49',plain,(
    ! [X8: $i] :
      ( ( l2_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('50',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['6','9','41','47','50'])).

thf('52',plain,(
    ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).


%------------------------------------------------------------------------------
