%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OhitqY92Je

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:37 EST 2020

% Result     : Theorem 14.71s
% Output     : Refutation 14.71s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 185 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  770 (3100 expanded)
%              Number of equality atoms :   23 (  95 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t51_lattices,conjecture,(
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
               => ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) )
                  = ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(dt_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( m1_subset_1 @ ( k4_lattices @ X2 @ X1 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattices])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( l1_lattices @ X6 )
      | ~ ( l3_lattices @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('25',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','22','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','28'])).

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

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( ( k7_lattices @ X8 @ ( k7_lattices @ X8 @ X7 ) )
        = X7 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v17_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_lattices])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ) )
      = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ) )
      = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('37',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t50_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k7_lattices @ A @ ( k4_lattices @ A @ B @ C ) )
                = ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( ( k7_lattices @ X10 @ ( k4_lattices @ X10 @ X9 @ X11 ) )
        = ( k3_lattices @ X10 @ ( k7_lattices @ X10 @ X9 ) @ ( k7_lattices @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v17_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t50_lattices])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
        = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( ( k7_lattices @ X8 @ ( k7_lattices @ X8 @ X7 ) )
        = X7 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v17_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_lattices])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) )
    = sk_B ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
        = ( k3_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
        = ( k3_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) )
    = ( k3_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','54'])).

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

thf('65',plain,
    ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) )
    = ( k3_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['55','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ sk_C ) )
      = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','65'])).

thf('67',plain,(
    ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ sk_C ) )
 != ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OhitqY92Je
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 14.71/14.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.71/14.89  % Solved by: fo/fo7.sh
% 14.71/14.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.71/14.89  % done 2572 iterations in 14.420s
% 14.71/14.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.71/14.89  % SZS output start Refutation
% 14.71/14.89  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 14.71/14.89  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 14.71/14.89  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 14.71/14.89  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 14.71/14.89  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 14.71/14.89  thf(sk_C_type, type, sk_C: $i).
% 14.71/14.89  thf(sk_B_type, type, sk_B: $i).
% 14.71/14.89  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 14.71/14.89  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 14.71/14.89  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 14.71/14.89  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 14.71/14.89  thf(sk_A_type, type, sk_A: $i).
% 14.71/14.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 14.71/14.89  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 14.71/14.89  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 14.71/14.89  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 14.71/14.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 14.71/14.89  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 14.71/14.89  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 14.71/14.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.71/14.89  thf(t51_lattices, conjecture,
% 14.71/14.89    (![A:$i]:
% 14.71/14.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.71/14.89         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 14.71/14.89       ( ![B:$i]:
% 14.71/14.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 14.71/14.89           ( ![C:$i]:
% 14.71/14.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.71/14.89               ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) ) =
% 14.71/14.89                 ( k4_lattices @
% 14.71/14.89                   A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 14.71/14.89  thf(zf_stmt_0, negated_conjecture,
% 14.71/14.89    (~( ![A:$i]:
% 14.71/14.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.71/14.89            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 14.71/14.89          ( ![B:$i]:
% 14.71/14.89            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 14.71/14.89              ( ![C:$i]:
% 14.71/14.89                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.71/14.89                  ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) ) =
% 14.71/14.89                    ( k4_lattices @
% 14.71/14.89                      A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ) )),
% 14.71/14.89    inference('cnf.neg', [status(esa)], [t51_lattices])).
% 14.71/14.89  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf(dt_k7_lattices, axiom,
% 14.71/14.89    (![A:$i,B:$i]:
% 14.71/14.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 14.71/14.89         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 14.71/14.89       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 14.71/14.89  thf('2', plain,
% 14.71/14.89      (![X4 : $i, X5 : $i]:
% 14.71/14.89         (~ (l3_lattices @ X4)
% 14.71/14.89          | (v2_struct_0 @ X4)
% 14.71/14.89          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 14.71/14.89          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 14.71/14.89      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 14.71/14.89  thf('3', plain,
% 14.71/14.89      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 14.71/14.89        | (v2_struct_0 @ sk_A)
% 14.71/14.89        | ~ (l3_lattices @ sk_A))),
% 14.71/14.89      inference('sup-', [status(thm)], ['1', '2'])).
% 14.71/14.89  thf('4', plain, ((l3_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('5', plain,
% 14.71/14.89      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 14.71/14.89        | (v2_struct_0 @ sk_A))),
% 14.71/14.89      inference('demod', [status(thm)], ['3', '4'])).
% 14.71/14.89  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('7', plain,
% 14.71/14.89      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('clc', [status(thm)], ['5', '6'])).
% 14.71/14.89  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('9', plain,
% 14.71/14.89      (![X4 : $i, X5 : $i]:
% 14.71/14.89         (~ (l3_lattices @ X4)
% 14.71/14.89          | (v2_struct_0 @ X4)
% 14.71/14.89          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 14.71/14.89          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 14.71/14.89      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 14.71/14.89  thf('10', plain,
% 14.71/14.89      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 14.71/14.89        | (v2_struct_0 @ sk_A)
% 14.71/14.89        | ~ (l3_lattices @ sk_A))),
% 14.71/14.89      inference('sup-', [status(thm)], ['8', '9'])).
% 14.71/14.89  thf('11', plain, ((l3_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('12', plain,
% 14.71/14.89      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 14.71/14.89        | (v2_struct_0 @ sk_A))),
% 14.71/14.89      inference('demod', [status(thm)], ['10', '11'])).
% 14.71/14.89  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('14', plain,
% 14.71/14.89      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('clc', [status(thm)], ['12', '13'])).
% 14.71/14.89  thf(dt_k4_lattices, axiom,
% 14.71/14.89    (![A:$i,B:$i,C:$i]:
% 14.71/14.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 14.71/14.89         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 14.71/14.89         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 14.71/14.89       ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 14.71/14.89  thf('15', plain,
% 14.71/14.89      (![X1 : $i, X2 : $i, X3 : $i]:
% 14.71/14.89         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 14.71/14.89          | ~ (l1_lattices @ X2)
% 14.71/14.89          | ~ (v6_lattices @ X2)
% 14.71/14.89          | (v2_struct_0 @ X2)
% 14.71/14.89          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 14.71/14.89          | (m1_subset_1 @ (k4_lattices @ X2 @ X1 @ X3) @ (u1_struct_0 @ X2)))),
% 14.71/14.89      inference('cnf', [status(esa)], [dt_k4_lattices])).
% 14.71/14.89  thf('16', plain,
% 14.71/14.89      (![X0 : $i]:
% 14.71/14.89         ((m1_subset_1 @ 
% 14.71/14.89           (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0) @ 
% 14.71/14.89           (u1_struct_0 @ sk_A))
% 14.71/14.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.71/14.89          | (v2_struct_0 @ sk_A)
% 14.71/14.89          | ~ (v6_lattices @ sk_A)
% 14.71/14.89          | ~ (l1_lattices @ sk_A))),
% 14.71/14.89      inference('sup-', [status(thm)], ['14', '15'])).
% 14.71/14.89  thf(cc1_lattices, axiom,
% 14.71/14.89    (![A:$i]:
% 14.71/14.89     ( ( l3_lattices @ A ) =>
% 14.71/14.89       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 14.71/14.89         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 14.71/14.89           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 14.71/14.89           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 14.71/14.89  thf('17', plain,
% 14.71/14.89      (![X0 : $i]:
% 14.71/14.89         ((v2_struct_0 @ X0)
% 14.71/14.89          | ~ (v10_lattices @ X0)
% 14.71/14.89          | (v6_lattices @ X0)
% 14.71/14.89          | ~ (l3_lattices @ X0))),
% 14.71/14.89      inference('cnf', [status(esa)], [cc1_lattices])).
% 14.71/14.89  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('19', plain,
% 14.71/14.89      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 14.71/14.89      inference('sup-', [status(thm)], ['17', '18'])).
% 14.71/14.89  thf('20', plain, ((l3_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('21', plain, ((v10_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('22', plain, ((v6_lattices @ sk_A)),
% 14.71/14.89      inference('demod', [status(thm)], ['19', '20', '21'])).
% 14.71/14.89  thf('23', plain, ((l3_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf(dt_l3_lattices, axiom,
% 14.71/14.89    (![A:$i]:
% 14.71/14.89     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 14.71/14.89  thf('24', plain, (![X6 : $i]: ((l1_lattices @ X6) | ~ (l3_lattices @ X6))),
% 14.71/14.89      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 14.71/14.89  thf('25', plain, ((l1_lattices @ sk_A)),
% 14.71/14.89      inference('sup-', [status(thm)], ['23', '24'])).
% 14.71/14.89  thf('26', plain,
% 14.71/14.89      (![X0 : $i]:
% 14.71/14.89         ((m1_subset_1 @ 
% 14.71/14.89           (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0) @ 
% 14.71/14.89           (u1_struct_0 @ sk_A))
% 14.71/14.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.71/14.89          | (v2_struct_0 @ sk_A))),
% 14.71/14.89      inference('demod', [status(thm)], ['16', '22', '25'])).
% 14.71/14.89  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('28', plain,
% 14.71/14.89      (![X0 : $i]:
% 14.71/14.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.71/14.89          | (m1_subset_1 @ 
% 14.71/14.89             (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0) @ 
% 14.71/14.89             (u1_struct_0 @ sk_A)))),
% 14.71/14.89      inference('clc', [status(thm)], ['26', '27'])).
% 14.71/14.89  thf('29', plain,
% 14.71/14.89      ((m1_subset_1 @ 
% 14.71/14.89        (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.89         (k7_lattices @ sk_A @ sk_C)) @ 
% 14.71/14.89        (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('sup-', [status(thm)], ['7', '28'])).
% 14.71/14.89  thf(t49_lattices, axiom,
% 14.71/14.89    (![A:$i]:
% 14.71/14.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.71/14.89         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 14.71/14.89       ( ![B:$i]:
% 14.71/14.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 14.71/14.89           ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) ) = ( B ) ) ) ) ))).
% 14.71/14.89  thf('30', plain,
% 14.71/14.89      (![X7 : $i, X8 : $i]:
% 14.71/14.89         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 14.71/14.89          | ((k7_lattices @ X8 @ (k7_lattices @ X8 @ X7)) = (X7))
% 14.71/14.89          | ~ (l3_lattices @ X8)
% 14.71/14.89          | ~ (v17_lattices @ X8)
% 14.71/14.89          | ~ (v10_lattices @ X8)
% 14.71/14.89          | (v2_struct_0 @ X8))),
% 14.71/14.89      inference('cnf', [status(esa)], [t49_lattices])).
% 14.71/14.89  thf('31', plain,
% 14.71/14.89      (((v2_struct_0 @ sk_A)
% 14.71/14.89        | ~ (v10_lattices @ sk_A)
% 14.71/14.89        | ~ (v17_lattices @ sk_A)
% 14.71/14.89        | ~ (l3_lattices @ sk_A)
% 14.71/14.89        | ((k7_lattices @ sk_A @ 
% 14.71/14.89            (k7_lattices @ sk_A @ 
% 14.71/14.89             (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.89              (k7_lattices @ sk_A @ sk_C))))
% 14.71/14.89            = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.89               (k7_lattices @ sk_A @ sk_C))))),
% 14.71/14.89      inference('sup-', [status(thm)], ['29', '30'])).
% 14.71/14.89  thf('32', plain, ((v10_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('33', plain, ((v17_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('34', plain, ((l3_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('35', plain,
% 14.71/14.89      (((v2_struct_0 @ sk_A)
% 14.71/14.89        | ((k7_lattices @ sk_A @ 
% 14.71/14.89            (k7_lattices @ sk_A @ 
% 14.71/14.89             (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.89              (k7_lattices @ sk_A @ sk_C))))
% 14.71/14.89            = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.89               (k7_lattices @ sk_A @ sk_C))))),
% 14.71/14.89      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 14.71/14.89  thf('36', plain,
% 14.71/14.89      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('clc', [status(thm)], ['5', '6'])).
% 14.71/14.89  thf('37', plain,
% 14.71/14.89      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('clc', [status(thm)], ['12', '13'])).
% 14.71/14.89  thf(t50_lattices, axiom,
% 14.71/14.89    (![A:$i]:
% 14.71/14.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.71/14.89         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 14.71/14.89       ( ![B:$i]:
% 14.71/14.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 14.71/14.89           ( ![C:$i]:
% 14.71/14.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.71/14.89               ( ( k7_lattices @ A @ ( k4_lattices @ A @ B @ C ) ) =
% 14.71/14.89                 ( k3_lattices @
% 14.71/14.89                   A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 14.71/14.89  thf('38', plain,
% 14.71/14.89      (![X9 : $i, X10 : $i, X11 : $i]:
% 14.71/14.89         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 14.71/14.89          | ((k7_lattices @ X10 @ (k4_lattices @ X10 @ X9 @ X11))
% 14.71/14.89              = (k3_lattices @ X10 @ (k7_lattices @ X10 @ X9) @ 
% 14.71/14.89                 (k7_lattices @ X10 @ X11)))
% 14.71/14.89          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 14.71/14.89          | ~ (l3_lattices @ X10)
% 14.71/14.89          | ~ (v17_lattices @ X10)
% 14.71/14.89          | ~ (v10_lattices @ X10)
% 14.71/14.89          | (v2_struct_0 @ X10))),
% 14.71/14.89      inference('cnf', [status(esa)], [t50_lattices])).
% 14.71/14.89  thf('39', plain,
% 14.71/14.89      (![X0 : $i]:
% 14.71/14.89         ((v2_struct_0 @ sk_A)
% 14.71/14.89          | ~ (v10_lattices @ sk_A)
% 14.71/14.89          | ~ (v17_lattices @ sk_A)
% 14.71/14.89          | ~ (l3_lattices @ sk_A)
% 14.71/14.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.71/14.89          | ((k7_lattices @ sk_A @ 
% 14.71/14.89              (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 14.71/14.89              = (k3_lattices @ sk_A @ 
% 14.71/14.89                 (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) @ 
% 14.71/14.89                 (k7_lattices @ sk_A @ X0))))),
% 14.71/14.89      inference('sup-', [status(thm)], ['37', '38'])).
% 14.71/14.89  thf('40', plain, ((v10_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('41', plain, ((v17_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('42', plain, ((l3_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('43', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('44', plain,
% 14.71/14.89      (![X7 : $i, X8 : $i]:
% 14.71/14.89         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 14.71/14.89          | ((k7_lattices @ X8 @ (k7_lattices @ X8 @ X7)) = (X7))
% 14.71/14.89          | ~ (l3_lattices @ X8)
% 14.71/14.89          | ~ (v17_lattices @ X8)
% 14.71/14.89          | ~ (v10_lattices @ X8)
% 14.71/14.89          | (v2_struct_0 @ X8))),
% 14.71/14.89      inference('cnf', [status(esa)], [t49_lattices])).
% 14.71/14.89  thf('45', plain,
% 14.71/14.89      (((v2_struct_0 @ sk_A)
% 14.71/14.89        | ~ (v10_lattices @ sk_A)
% 14.71/14.89        | ~ (v17_lattices @ sk_A)
% 14.71/14.89        | ~ (l3_lattices @ sk_A)
% 14.71/14.89        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) = (sk_B)))),
% 14.71/14.89      inference('sup-', [status(thm)], ['43', '44'])).
% 14.71/14.89  thf('46', plain, ((v10_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('47', plain, ((v17_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('48', plain, ((l3_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('49', plain,
% 14.71/14.89      (((v2_struct_0 @ sk_A)
% 14.71/14.89        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) = (sk_B)))),
% 14.71/14.89      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 14.71/14.89  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('51', plain,
% 14.71/14.89      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) = (sk_B))),
% 14.71/14.89      inference('clc', [status(thm)], ['49', '50'])).
% 14.71/14.89  thf('52', plain,
% 14.71/14.89      (![X0 : $i]:
% 14.71/14.89         ((v2_struct_0 @ sk_A)
% 14.71/14.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.71/14.89          | ((k7_lattices @ sk_A @ 
% 14.71/14.89              (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 14.71/14.89              = (k3_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ X0))))),
% 14.71/14.89      inference('demod', [status(thm)], ['39', '40', '41', '42', '51'])).
% 14.71/14.89  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('54', plain,
% 14.71/14.89      (![X0 : $i]:
% 14.71/14.89         (((k7_lattices @ sk_A @ 
% 14.71/14.89            (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 14.71/14.89            = (k3_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ X0)))
% 14.71/14.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 14.71/14.89      inference('clc', [status(thm)], ['52', '53'])).
% 14.71/14.89  thf('55', plain,
% 14.71/14.89      (((k7_lattices @ sk_A @ 
% 14.71/14.89         (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.89          (k7_lattices @ sk_A @ sk_C)))
% 14.71/14.89         = (k3_lattices @ sk_A @ sk_B @ 
% 14.71/14.89            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C))))),
% 14.71/14.89      inference('sup-', [status(thm)], ['36', '54'])).
% 14.71/14.89  thf('56', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('57', plain,
% 14.71/14.89      (![X7 : $i, X8 : $i]:
% 14.71/14.89         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 14.71/14.89          | ((k7_lattices @ X8 @ (k7_lattices @ X8 @ X7)) = (X7))
% 14.71/14.89          | ~ (l3_lattices @ X8)
% 14.71/14.89          | ~ (v17_lattices @ X8)
% 14.71/14.89          | ~ (v10_lattices @ X8)
% 14.71/14.89          | (v2_struct_0 @ X8))),
% 14.71/14.89      inference('cnf', [status(esa)], [t49_lattices])).
% 14.71/14.89  thf('58', plain,
% 14.71/14.89      (((v2_struct_0 @ sk_A)
% 14.71/14.89        | ~ (v10_lattices @ sk_A)
% 14.71/14.89        | ~ (v17_lattices @ sk_A)
% 14.71/14.89        | ~ (l3_lattices @ sk_A)
% 14.71/14.89        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C)))),
% 14.71/14.89      inference('sup-', [status(thm)], ['56', '57'])).
% 14.71/14.89  thf('59', plain, ((v10_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('60', plain, ((v17_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('61', plain, ((l3_lattices @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('62', plain,
% 14.71/14.89      (((v2_struct_0 @ sk_A)
% 14.71/14.89        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C)))),
% 14.71/14.89      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 14.71/14.89  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 14.71/14.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.89  thf('64', plain,
% 14.71/14.89      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C))),
% 14.71/14.89      inference('clc', [status(thm)], ['62', '63'])).
% 14.71/14.89  thf('65', plain,
% 14.71/14.89      (((k7_lattices @ sk_A @ 
% 14.71/14.89         (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.89          (k7_lattices @ sk_A @ sk_C)))
% 14.71/14.89         = (k3_lattices @ sk_A @ sk_B @ sk_C))),
% 14.71/14.89      inference('demod', [status(thm)], ['55', '64'])).
% 14.71/14.89  thf('66', plain,
% 14.71/14.89      (((v2_struct_0 @ sk_A)
% 14.71/14.90        | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B @ sk_C))
% 14.71/14.90            = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.90               (k7_lattices @ sk_A @ sk_C))))),
% 14.71/14.90      inference('demod', [status(thm)], ['35', '65'])).
% 14.71/14.90  thf('67', plain,
% 14.71/14.90      (((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B @ sk_C))
% 14.71/14.90         != (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 14.71/14.90             (k7_lattices @ sk_A @ sk_C)))),
% 14.71/14.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.71/14.90  thf('68', plain, ((v2_struct_0 @ sk_A)),
% 14.71/14.90      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 14.71/14.90  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 14.71/14.90  
% 14.71/14.90  % SZS output end Refutation
% 14.71/14.90  
% 14.71/14.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
