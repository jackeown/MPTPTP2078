%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.27tJQIQHrs

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 167 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  699 (2572 expanded)
%              Number of equality atoms :   24 (  25 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

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

thf(commutativity_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k4_lattices @ A @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k4_lattices @ X2 @ X1 @ X3 )
        = ( k4_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( l1_lattices @ X6 )
      | ~ ( l3_lattices @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('19',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','16','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( ( k7_lattices @ X8 @ ( k7_lattices @ X8 @ X7 ) )
        = X7 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v17_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_lattices])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) )
    = sk_C ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r3_lattices @ X10 @ X9 @ ( k7_lattices @ X10 @ X11 ) )
      | ( ( k4_lattices @ X10 @ X9 @ X11 )
        = ( k5_lattices @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v17_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_lattices])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k5_lattices @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k5_lattices @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ sk_C )
    | ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
      = ( k5_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    r3_lattices @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('43',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
      = ( k5_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k5_lattices @ sk_A )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( ( k4_lattices @ X10 @ X9 @ X11 )
       != ( k5_lattices @ X10 ) )
      | ( r3_lattices @ X10 @ X9 @ ( k7_lattices @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v17_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_lattices])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
       != ( k5_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
       != ( k5_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.27tJQIQHrs
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 109 iterations in 0.061s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.51  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.51  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.51  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.51  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.21/0.51  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.51  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.51  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.51  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.21/0.51  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.51  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.51  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(t53_lattices, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( r3_lattices @ A @ B @ C ) =>
% 0.21/0.51                 ( r3_lattices @
% 0.21/0.51                   A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                  ( ( r3_lattices @ A @ B @ C ) =>
% 0.21/0.51                    ( r3_lattices @
% 0.21/0.51                      A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t53_lattices])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (~ (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.51          (k7_lattices @ sk_A @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k7_lattices, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (l3_lattices @ X4)
% 0.21/0.51          | (v2_struct_0 @ X4)
% 0.21/0.51          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.51          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l3_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(commutativity_k4_lattices, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.51         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (l1_lattices @ X2)
% 0.21/0.51          | ~ (v6_lattices @ X2)
% 0.21/0.51          | (v2_struct_0 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ((k4_lattices @ X2 @ X1 @ X3) = (k4_lattices @ X2 @ X3 @ X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k4_lattices @ sk_A @ sk_B @ X0) = (k4_lattices @ sk_A @ X0 @ sk_B))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v6_lattices @ sk_A)
% 0.21/0.51          | ~ (l1_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf(cc1_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l3_lattices @ A ) =>
% 0.21/0.51       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.51         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.51           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.51           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v6_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain, ((v6_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.51  thf('17', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l3_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.51  thf('18', plain, (![X6 : $i]: ((l1_lattices @ X6) | ~ (l3_lattices @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.51  thf('19', plain, ((l1_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k4_lattices @ sk_A @ sk_B @ X0) = (k4_lattices @ sk_A @ X0 @ sk_B))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '16', '19'])).
% 0.21/0.51  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ((k4_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.51              = (k4_lattices @ sk_A @ X0 @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C))
% 0.21/0.51         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '22'])).
% 0.21/0.51  thf('24', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t49_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ((k7_lattices @ X8 @ (k7_lattices @ X8 @ X7)) = (X7))
% 0.21/0.51          | ~ (l3_lattices @ X8)
% 0.21/0.51          | ~ (v17_lattices @ X8)
% 0.21/0.51          | ~ (v10_lattices @ X8)
% 0.21/0.51          | (v2_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t49_lattices])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v10_lattices @ sk_A)
% 0.21/0.51        | ~ (v17_lattices @ sk_A)
% 0.21/0.51        | ~ (l3_lattices @ sk_A)
% 0.21/0.51        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, ((v17_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.21/0.51  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C)) = (sk_C))),
% 0.21/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t52_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( ( k4_lattices @ A @ B @ C ) = ( k5_lattices @ A ) ) <=>
% 0.21/0.51                 ( r3_lattices @ A @ B @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.51          | ~ (r3_lattices @ X10 @ X9 @ (k7_lattices @ X10 @ X11))
% 0.21/0.51          | ((k4_lattices @ X10 @ X9 @ X11) = (k5_lattices @ X10))
% 0.21/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.51          | ~ (l3_lattices @ X10)
% 0.21/0.51          | ~ (v17_lattices @ X10)
% 0.21/0.51          | ~ (v10_lattices @ X10)
% 0.21/0.51          | (v2_struct_0 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t52_lattices])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v10_lattices @ sk_A)
% 0.21/0.51          | ~ (v17_lattices @ sk_A)
% 0.21/0.51          | ~ (l3_lattices @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ((k4_lattices @ sk_A @ sk_B @ X0) = (k5_lattices @ sk_A))
% 0.21/0.51          | ~ (r3_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain, ((v17_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ((k4_lattices @ sk_A @ sk_B @ X0) = (k5_lattices @ sk_A))
% 0.21/0.51          | ~ (r3_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((~ (r3_lattices @ sk_A @ sk_B @ sk_C)
% 0.21/0.51        | ((k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C))
% 0.21/0.51            = (k5_lattices @ sk_A))
% 0.21/0.51        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '39'])).
% 0.21/0.51  thf('41', plain, ((r3_lattices @ sk_A @ sk_B @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((((k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C))
% 0.21/0.51          = (k5_lattices @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.51  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((k4_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_C))
% 0.21/0.51         = (k5_lattices @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((k5_lattices @ sk_A)
% 0.21/0.51         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.51          | ((k4_lattices @ X10 @ X9 @ X11) != (k5_lattices @ X10))
% 0.21/0.51          | (r3_lattices @ X10 @ X9 @ (k7_lattices @ X10 @ X11))
% 0.21/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.51          | ~ (l3_lattices @ X10)
% 0.21/0.51          | ~ (v17_lattices @ X10)
% 0.21/0.51          | ~ (v10_lattices @ X10)
% 0.21/0.51          | (v2_struct_0 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t52_lattices])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v10_lattices @ sk_A)
% 0.21/0.51          | ~ (v17_lattices @ sk_A)
% 0.21/0.51          | ~ (l3_lattices @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.51             (k7_lattices @ sk_A @ X0))
% 0.21/0.51          | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.21/0.51              != (k5_lattices @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain, ((v17_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('52', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.51             (k7_lattices @ sk_A @ X0))
% 0.21/0.51          | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.21/0.51              != (k5_lattices @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 0.21/0.51        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.51           (k7_lattices @ sk_A @ sk_B))
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '53'])).
% 0.21/0.51  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 0.21/0.51        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.51           (k7_lattices @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.51           (k7_lattices @ sk_A @ sk_B)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.51  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.21/0.51        (k7_lattices @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
