%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1208+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QOb1vjgQP1

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 176 expanded)
%              Number of leaves         :   28 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  767 (1934 expanded)
%              Number of equality atoms :   38 (  92 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t43_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v14_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_lattices])).

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

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v9_lattices @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k2_lattices @ X7 @ X9 @ ( k1_lattices @ X7 @ X9 @ X8 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) )
        = X1 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) )
      = sk_B_1 )
    | ~ ( v9_lattices @ sk_A ) ),
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

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf(d17_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( ( v14_lattices @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( B
                = ( k6_lattices @ A ) )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( ( k1_lattices @ A @ B @ C )
                      = B )
                    & ( ( k1_lattices @ A @ C @ B )
                      = B ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v14_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( X5
       != ( k6_lattices @ X4 ) )
      | ( ( k1_lattices @ X4 @ X6 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d17_lattices])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l2_lattices @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( ( k1_lattices @ X4 @ X6 @ ( k6_lattices @ X4 ) )
        = ( k6_lattices @ X4 ) )
      | ~ ( m1_subset_1 @ ( k6_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v14_lattices @ X4 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( v14_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    v14_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['6','9','10','22','28'])).

thf('30',plain,(
    ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k4_lattices @ X2 @ X1 @ X3 )
        = ( k4_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( l1_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('43',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','40','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['30','51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_lattices @ X13 )
      | ~ ( v6_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattices @ X13 @ X12 @ X14 )
        = ( k2_lattices @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('58',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['52','66'])).

thf('68',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['29','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).


%------------------------------------------------------------------------------
