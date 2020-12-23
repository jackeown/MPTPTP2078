%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5SkmG2VjC3

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 145 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 (1614 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(cc1_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v7_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v1_tdlat_3 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_1])).

thf(t24_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) )
           => ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) )
              & ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) )
             => ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) )
                & ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tex_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('3',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('13',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X3 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('21',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','29'])).

thf('31',plain,
    ( ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
   <= ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( $false
   <= ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v7_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_tdlat_3 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_1])).

thf('35',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
   <= ~ ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('44',plain,(
    v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('46',plain,(
    ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['33','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5SkmG2VjC3
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 32 iterations in 0.015s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.47  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.20/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.47  thf(cc1_tex_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) =>
% 0.20/0.47         ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X2 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X2)
% 0.20/0.47          | ~ (v7_struct_0 @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v1_tdlat_3 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc1_tex_1])).
% 0.20/0.47  thf(t24_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47           ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) ) =>
% 0.20/0.47             ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.47               ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47              ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) ) =>
% 0.20/0.47                ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.47                  ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t24_tex_2])).
% 0.20/0.47  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k1_tex_2, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.47         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.47         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.47         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X3)
% 0.20/0.47          | (v2_struct_0 @ X3)
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.47          | ~ (v2_struct_0 @ (k1_tex_2 @ X3 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '7'])).
% 0.20/0.47  thf('9', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(fc2_tex_2, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.47         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.47         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.47         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X5)
% 0.20/0.47          | (v2_struct_0 @ X5)
% 0.20/0.47          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.47          | (v7_struct_0 @ (k1_tex_2 @ X5 @ X6)))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '17'])).
% 0.20/0.47  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X3)
% 0.20/0.47          | (v2_struct_0 @ X3)
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.47          | (m1_pre_topc @ (k1_tex_2 @ X3 @ X4) @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf(dt_m1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))
% 0.20/0.47         <= (~ ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['31'])).
% 0.20/0.47  thf('33', plain, (($false) <= (~ ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X2 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X2)
% 0.20/0.47          | ~ (v7_struct_0 @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v2_tdlat_3 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc1_tex_1])).
% 0.20/0.47  thf('35', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.47  thf('37', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.47  thf('39', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.47  thf('41', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('42', plain, ((v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      ((~ (v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))
% 0.20/0.47         <= (~ ((v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['31'])).
% 0.20/0.47  thf('44', plain, (((v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (~ ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))) | 
% 0.20/0.47       ~ ((v2_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['31'])).
% 0.20/0.47  thf('46', plain, (~ ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain, ($false),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['33', '46'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
