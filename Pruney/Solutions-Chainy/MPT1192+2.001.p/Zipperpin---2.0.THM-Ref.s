%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f2m5A8svUq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:30 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 208 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  795 (2631 expanded)
%              Number of equality atoms :   36 ( 111 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t17_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k1_lattices @ A @ B @ B )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v6_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k1_lattices @ A @ B @ B )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k1_lattices @ X10 @ X9 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattices])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( l2_lattices @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('6',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v8_lattices @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( ( k1_lattices @ X3 @ ( k2_lattices @ X3 @ X5 @ X4 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_2 ) @ sk_B_2 )
        = sk_B_2 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_2 ) @ sk_B_2 )
        = sk_B_2 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_2 ) @ sk_B_2 )
        = sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ sk_B_2 ) @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( l1_lattices @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('27',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ sk_B_2 )
    = ( k2_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( ( k4_lattices @ X1 @ X0 @ X2 )
        = ( k4_lattices @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) )
    = ( k4_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) )
    = ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v9_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) )
                  = B ) ) ) ) ) )).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v9_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k2_lattices @ X6 @ X8 @ ( k1_lattices @ X6 @ X8 @ X7 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v9_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['51','61'])).

thf('63',plain,
    ( sk_B_2
    = ( k4_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['41','62'])).

thf('64',plain,
    ( sk_B_2
    = ( k2_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['31','63'])).

thf('65',plain,
    ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
    = sk_B_2 ),
    inference(demod,[status(thm)],['19','64'])).

thf('66',plain,(
    ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f2m5A8svUq
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 104 iterations in 0.205s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.48/0.66  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.48/0.66  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.48/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.66  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.48/0.66  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.48/0.66  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.48/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.66  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.48/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.66  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.48/0.66  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.48/0.66  thf(t17_lattices, conjecture,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.48/0.66         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.48/0.66       ( ![B:$i]:
% 0.48/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.66           ( ( k1_lattices @ A @ B @ B ) = ( B ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i]:
% 0.48/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.48/0.66            ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.48/0.66          ( ![B:$i]:
% 0.48/0.66            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.66              ( ( k1_lattices @ A @ B @ B ) = ( B ) ) ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t17_lattices])).
% 0.48/0.66  thf('0', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(dt_k1_lattices, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) & 
% 0.48/0.66         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.48/0.66         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.66       ( m1_subset_1 @ ( k1_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.48/0.66          | ~ (l2_lattices @ X10)
% 0.48/0.66          | (v2_struct_0 @ X10)
% 0.48/0.66          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.48/0.66          | (m1_subset_1 @ (k1_lattices @ X10 @ X9 @ X11) @ (u1_struct_0 @ X10)))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k1_lattices])).
% 0.48/0.66  thf('3', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 0.48/0.66           (u1_struct_0 @ sk_A))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (l2_lattices @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.66  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(dt_l3_lattices, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.48/0.66  thf('5', plain, (![X12 : $i]: ((l2_lattices @ X12) | ~ (l3_lattices @ X12))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.48/0.66  thf('6', plain, ((l2_lattices @ sk_A)),
% 0.48/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 0.48/0.66           (u1_struct_0 @ sk_A))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (v2_struct_0 @ sk_A))),
% 0.48/0.66      inference('demod', [status(thm)], ['3', '6'])).
% 0.48/0.66  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('9', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 0.48/0.66             (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66        (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['0', '9'])).
% 0.48/0.66  thf('11', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(d8_lattices, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.48/0.66       ( ( v8_lattices @ A ) <=>
% 0.48/0.66         ( ![B:$i]:
% 0.48/0.66           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.66             ( ![C:$i]:
% 0.48/0.66               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.66                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 0.48/0.66                   ( C ) ) ) ) ) ) ) ))).
% 0.48/0.66  thf('12', plain,
% 0.48/0.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.66         (~ (v8_lattices @ X3)
% 0.48/0.66          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.48/0.66          | ((k1_lattices @ X3 @ (k2_lattices @ X3 @ X5 @ X4) @ X4) = (X4))
% 0.48/0.66          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.48/0.66          | ~ (l3_lattices @ X3)
% 0.48/0.66          | (v2_struct_0 @ X3))),
% 0.48/0.66      inference('cnf', [status(esa)], [d8_lattices])).
% 0.48/0.66  thf('13', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (l3_lattices @ sk_A)
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ sk_B_2)
% 0.48/0.66              = (sk_B_2))
% 0.48/0.66          | ~ (v8_lattices @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.48/0.66  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('15', plain, ((v8_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('16', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ sk_B_2)
% 0.48/0.66              = (sk_B_2)))),
% 0.48/0.66      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.48/0.66  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('18', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ sk_B_2)
% 0.48/0.66            = (sk_B_2))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('clc', [status(thm)], ['16', '17'])).
% 0.48/0.66  thf('19', plain,
% 0.48/0.66      (((k1_lattices @ sk_A @ 
% 0.48/0.66         (k2_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ sk_B_2) @ 
% 0.48/0.66         sk_B_2) = (sk_B_2))),
% 0.48/0.66      inference('sup-', [status(thm)], ['10', '18'])).
% 0.48/0.66  thf('20', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('21', plain,
% 0.48/0.66      ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66        (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['0', '9'])).
% 0.48/0.66  thf(redefinition_k4_lattices, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.48/0.66         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.48/0.66         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.66       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.48/0.66  thf('22', plain,
% 0.48/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.48/0.66          | ~ (l1_lattices @ X14)
% 0.48/0.66          | ~ (v6_lattices @ X14)
% 0.48/0.66          | (v2_struct_0 @ X14)
% 0.48/0.66          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.48/0.66          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.48/0.66  thf('23', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k4_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ X0)
% 0.48/0.66            = (k2_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ X0))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (v6_lattices @ sk_A)
% 0.48/0.66          | ~ (l1_lattices @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.66  thf('24', plain, ((v6_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('25', plain, ((l3_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('26', plain,
% 0.48/0.66      (![X12 : $i]: ((l1_lattices @ X12) | ~ (l3_lattices @ X12))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.48/0.66  thf('27', plain, ((l1_lattices @ sk_A)),
% 0.48/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.66  thf('28', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k4_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ X0)
% 0.48/0.66            = (k2_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ X0))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (v2_struct_0 @ sk_A))),
% 0.48/0.66      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.48/0.66  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('30', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | ((k4_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ X0)
% 0.48/0.66              = (k2_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66                 X0)))),
% 0.48/0.66      inference('clc', [status(thm)], ['28', '29'])).
% 0.48/0.66  thf('31', plain,
% 0.48/0.66      (((k4_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ sk_B_2)
% 0.48/0.66         = (k2_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66            sk_B_2))),
% 0.48/0.66      inference('sup-', [status(thm)], ['20', '30'])).
% 0.48/0.66  thf('32', plain,
% 0.48/0.66      ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66        (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['0', '9'])).
% 0.48/0.66  thf('33', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(commutativity_k4_lattices, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.48/0.66         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.48/0.66         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.66       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 0.48/0.66  thf('34', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.48/0.66          | ~ (l1_lattices @ X1)
% 0.48/0.66          | ~ (v6_lattices @ X1)
% 0.48/0.66          | (v2_struct_0 @ X1)
% 0.48/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.48/0.66          | ((k4_lattices @ X1 @ X0 @ X2) = (k4_lattices @ X1 @ X2 @ X0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.48/0.66  thf('35', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.48/0.66            = (k4_lattices @ sk_A @ X0 @ sk_B_2))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (v6_lattices @ sk_A)
% 0.48/0.66          | ~ (l1_lattices @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.66  thf('36', plain, ((v6_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('37', plain, ((l1_lattices @ sk_A)),
% 0.48/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.66  thf('38', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.48/0.66            = (k4_lattices @ sk_A @ X0 @ sk_B_2))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (v2_struct_0 @ sk_A))),
% 0.48/0.66      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.48/0.66  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('40', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.48/0.66              = (k4_lattices @ sk_A @ X0 @ sk_B_2)))),
% 0.48/0.66      inference('clc', [status(thm)], ['38', '39'])).
% 0.48/0.66  thf('41', plain,
% 0.48/0.66      (((k4_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2))
% 0.48/0.66         = (k4_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66            sk_B_2))),
% 0.48/0.66      inference('sup-', [status(thm)], ['32', '40'])).
% 0.48/0.66  thf('42', plain,
% 0.48/0.66      ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66        (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['0', '9'])).
% 0.48/0.66  thf('43', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('44', plain,
% 0.48/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.48/0.66          | ~ (l1_lattices @ X14)
% 0.48/0.66          | ~ (v6_lattices @ X14)
% 0.48/0.66          | (v2_struct_0 @ X14)
% 0.48/0.66          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.48/0.66          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.48/0.66  thf('45', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.48/0.66            = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (v6_lattices @ sk_A)
% 0.48/0.66          | ~ (l1_lattices @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.66  thf('46', plain, ((v6_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('47', plain, ((l1_lattices @ sk_A)),
% 0.48/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.66  thf('48', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.48/0.66            = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | (v2_struct_0 @ sk_A))),
% 0.48/0.66      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.48/0.66  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('50', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.48/0.66              = (k2_lattices @ sk_A @ sk_B_2 @ X0)))),
% 0.48/0.66      inference('clc', [status(thm)], ['48', '49'])).
% 0.48/0.66  thf('51', plain,
% 0.48/0.66      (((k4_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2))
% 0.48/0.66         = (k2_lattices @ sk_A @ sk_B_2 @ 
% 0.48/0.66            (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['42', '50'])).
% 0.48/0.66  thf('52', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('53', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(d9_lattices, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.48/0.66       ( ( v9_lattices @ A ) <=>
% 0.48/0.66         ( ![B:$i]:
% 0.48/0.66           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.66             ( ![C:$i]:
% 0.48/0.66               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.66                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 0.48/0.66                   ( B ) ) ) ) ) ) ) ))).
% 0.48/0.66  thf('54', plain,
% 0.48/0.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.66         (~ (v9_lattices @ X6)
% 0.48/0.66          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.48/0.66          | ((k2_lattices @ X6 @ X8 @ (k1_lattices @ X6 @ X8 @ X7)) = (X8))
% 0.48/0.66          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.48/0.66          | ~ (l3_lattices @ X6)
% 0.48/0.66          | (v2_struct_0 @ X6))),
% 0.48/0.66      inference('cnf', [status(esa)], [d9_lattices])).
% 0.48/0.66  thf('55', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (l3_lattices @ sk_A)
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.48/0.66              = (X0))
% 0.48/0.66          | ~ (v9_lattices @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.66  thf('56', plain, ((l3_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('57', plain, ((v9_lattices @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('58', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.48/0.66          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.48/0.66              = (X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.48/0.66  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('60', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.48/0.66            = (X0))
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('clc', [status(thm)], ['58', '59'])).
% 0.48/0.66  thf('61', plain,
% 0.48/0.66      (((k2_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2))
% 0.48/0.66         = (sk_B_2))),
% 0.48/0.66      inference('sup-', [status(thm)], ['52', '60'])).
% 0.48/0.66  thf('62', plain,
% 0.48/0.66      (((k4_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2))
% 0.48/0.66         = (sk_B_2))),
% 0.48/0.66      inference('sup+', [status(thm)], ['51', '61'])).
% 0.48/0.66  thf('63', plain,
% 0.48/0.66      (((sk_B_2)
% 0.48/0.66         = (k4_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66            sk_B_2))),
% 0.48/0.66      inference('demod', [status(thm)], ['41', '62'])).
% 0.48/0.66  thf('64', plain,
% 0.48/0.66      (((sk_B_2)
% 0.48/0.66         = (k2_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) @ 
% 0.48/0.66            sk_B_2))),
% 0.48/0.66      inference('demod', [status(thm)], ['31', '63'])).
% 0.48/0.66  thf('65', plain, (((k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) = (sk_B_2))),
% 0.48/0.66      inference('demod', [status(thm)], ['19', '64'])).
% 0.48/0.66  thf('66', plain, (((k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) != (sk_B_2))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('67', plain, ($false),
% 0.48/0.66      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
