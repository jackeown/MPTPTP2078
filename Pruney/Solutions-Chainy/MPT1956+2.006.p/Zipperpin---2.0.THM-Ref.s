%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e29jK8ouRP

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 183 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  621 (2829 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t3_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( r3_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) )
            & ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( r3_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) )
              & ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_waybel_7])).

thf('0',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r2_yellow_0 @ A @ B )
          & ( r1_yellow_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_yellow_0 @ X6 @ X8 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v3_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ~ ( v2_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('11',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['8','13'])).

thf(t34_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r1_yellow_0 @ A @ B )
            & ( r1_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_orders_2 @ X9 @ ( k1_yellow_0 @ X9 @ X10 ) @ ( k1_yellow_0 @ X9 @ X11 ) )
      | ~ ( r1_yellow_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_yellow_0 @ X9 @ X10 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X1 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['8','13'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X1 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('33',plain,(
    r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
   <= ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_yellow_0 @ X6 @ X7 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v3_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(t35_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r2_yellow_0 @ A @ B )
            & ( r2_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_orders_2 @ X12 @ ( k2_yellow_0 @ X12 @ X13 ) @ ( k2_yellow_0 @ X12 @ X14 ) )
      | ~ ( r2_yellow_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( r2_yellow_0 @ X12 @ X14 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( k2_yellow_0 @ sk_A @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( k2_yellow_0 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['38','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e29jK8ouRP
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:23:52 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 29 iterations in 0.023s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.50  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(v3_lattice3_type, type, v3_lattice3: $i > $o).
% 0.21/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.50  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.21/0.50  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.21/0.50  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.21/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.50  thf(t3_waybel_7, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.21/0.50         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.21/0.50         ( l1_orders_2 @ A ) ) =>
% 0.21/0.50       ( ![B:$i,C:$i]:
% 0.21/0.50         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.50           ( ( r3_orders_2 @
% 0.21/0.50               A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.50             ( r1_orders_2 @
% 0.21/0.50               A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.21/0.50            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.21/0.50            ( l1_orders_2 @ A ) ) =>
% 0.21/0.50          ( ![B:$i,C:$i]:
% 0.21/0.50            ( ( r1_tarski @ B @ C ) =>
% 0.21/0.50              ( ( r3_orders_2 @
% 0.21/0.50                  A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.50                ( r1_orders_2 @
% 0.21/0.50                  A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t3_waybel_7])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.50        | ~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.50             (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.50           (k2_yellow_0 @ sk_A @ sk_B)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.50               (k2_yellow_0 @ sk_A @ sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t17_yellow_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.21/0.50         ( v3_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]: ( ( r2_yellow_0 @ A @ B ) & ( r1_yellow_0 @ A @ B ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X6 : $i, X8 : $i]:
% 0.21/0.50         ((r1_yellow_0 @ X6 @ X8)
% 0.21/0.50          | ~ (l1_orders_2 @ X6)
% 0.21/0.50          | ~ (v3_lattice3 @ X6)
% 0.21/0.50          | ~ (v5_orders_2 @ X6)
% 0.21/0.50          | (v2_struct_0 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.50          | ~ (v3_lattice3 @ sk_A)
% 0.21/0.50          | (r1_yellow_0 @ sk_A @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, ((v3_lattice3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r1_yellow_0 @ sk_A @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.50  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_lattice3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X3 : $i]:
% 0.21/0.50         (~ (v2_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.21/0.50  thf('11', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v2_lattice3 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain, ((v2_lattice3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain, (![X0 : $i]: (r1_yellow_0 @ sk_A @ X0)),
% 0.21/0.50      inference('clc', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf(t34_yellow_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( ![B:$i,C:$i]:
% 0.21/0.50         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 0.21/0.50             ( r1_yellow_0 @ A @ C ) ) =>
% 0.21/0.50           ( r1_orders_2 @
% 0.21/0.50             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         ((r1_orders_2 @ X9 @ (k1_yellow_0 @ X9 @ X10) @ 
% 0.21/0.50           (k1_yellow_0 @ X9 @ X11))
% 0.21/0.50          | ~ (r1_yellow_0 @ X9 @ X11)
% 0.21/0.50          | ~ (r1_tarski @ X10 @ X11)
% 0.21/0.50          | ~ (r1_yellow_0 @ X9 @ X10)
% 0.21/0.50          | ~ (l1_orders_2 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t34_yellow_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_A)
% 0.21/0.50          | ~ (r1_yellow_0 @ sk_A @ X1)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.50          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X1) @ 
% 0.21/0.50             (k1_yellow_0 @ sk_A @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain, (![X0 : $i]: (r1_yellow_0 @ sk_A @ X0)),
% 0.21/0.50      inference('clc', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.50          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X1) @ 
% 0.21/0.50             (k1_yellow_0 @ sk_A @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50        (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '19'])).
% 0.21/0.50  thf(dt_k1_yellow_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X4)
% 0.21/0.50          | (m1_subset_1 @ (k1_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X4)
% 0.21/0.50          | (m1_subset_1 @ (k1_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.50  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.50         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (l1_orders_2 @ X1)
% 0.21/0.50          | ~ (v3_orders_2 @ X1)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.50          | (r3_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.50          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X0)
% 0.21/0.50          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.50          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v3_orders_2 @ X0)
% 0.21/0.50          | ~ (l1_orders_2 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v3_orders_2 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.50          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.50          | ~ (l1_orders_2 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X0)
% 0.21/0.50          | ~ (l1_orders_2 @ X0)
% 0.21/0.50          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.50               (k1_yellow_0 @ X0 @ X1))
% 0.21/0.50          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.50             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v3_orders_2 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v3_orders_2 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.50             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.50          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.50               (k1_yellow_0 @ X0 @ X1))
% 0.21/0.50          | ~ (l1_orders_2 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.50        | (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v3_orders_2 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '27'])).
% 0.21/0.50  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.50  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50        (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50           (k1_yellow_0 @ sk_A @ sk_C)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50               (k1_yellow_0 @ sk_A @ sk_C))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k1_yellow_0 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.50         (k2_yellow_0 @ sk_A @ sk_B))) | 
% 0.21/0.50       ~
% 0.21/0.50       ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k1_yellow_0 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.50         (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.50          (k2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 0.21/0.50  thf('39', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         ((r2_yellow_0 @ X6 @ X7)
% 0.21/0.50          | ~ (l1_orders_2 @ X6)
% 0.21/0.50          | ~ (v3_lattice3 @ X6)
% 0.21/0.50          | ~ (v5_orders_2 @ X6)
% 0.21/0.50          | (v2_struct_0 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.50          | ~ (v3_lattice3 @ sk_A)
% 0.21/0.50          | (r2_yellow_0 @ sk_A @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain, ((v3_lattice3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r2_yellow_0 @ sk_A @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('47', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.21/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf(t35_yellow_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( ![B:$i,C:$i]:
% 0.21/0.50         ( ( ( r1_tarski @ B @ C ) & ( r2_yellow_0 @ A @ B ) & 
% 0.21/0.50             ( r2_yellow_0 @ A @ C ) ) =>
% 0.21/0.50           ( r1_orders_2 @
% 0.21/0.50             A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ))).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         ((r1_orders_2 @ X12 @ (k2_yellow_0 @ X12 @ X13) @ 
% 0.21/0.50           (k2_yellow_0 @ X12 @ X14))
% 0.21/0.50          | ~ (r2_yellow_0 @ X12 @ X13)
% 0.21/0.50          | ~ (r1_tarski @ X14 @ X13)
% 0.21/0.50          | ~ (r2_yellow_0 @ X12 @ X14)
% 0.21/0.50          | ~ (l1_orders_2 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t35_yellow_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_A)
% 0.21/0.50          | ~ (r2_yellow_0 @ sk_A @ X1)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.50          | (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ X0) @ 
% 0.21/0.50             (k2_yellow_0 @ sk_A @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.21/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.50          | (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ X0) @ 
% 0.21/0.50             (k2_yellow_0 @ sk_A @ X1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.50        (k2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '52'])).
% 0.21/0.50  thf('54', plain, ($false), inference('demod', [status(thm)], ['38', '53'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
