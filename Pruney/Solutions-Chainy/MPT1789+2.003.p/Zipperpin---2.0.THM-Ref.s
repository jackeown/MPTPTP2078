%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4nAsLZWIeg

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 188 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  645 (2877 expanded)
%              Number of equality atoms :   50 ( 206 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(t104_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
                = ( u1_struct_0 @ A ) )
              & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
                = ( k5_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t104_tmap_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k6_tmap_1 @ X7 @ X6 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( k5_tmap_1 @ X7 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_pre_topc @ X4 @ X5 )
       != ( g1_pre_topc @ X2 @ X3 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('17',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('25',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['14','22','30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_pre_topc @ X4 @ X5 )
       != ( g1_pre_topc @ X2 @ X3 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
    | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('43',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('44',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('45',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('46',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('48',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('51',plain,(
    ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['33','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4nAsLZWIeg
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 31 iterations in 0.021s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.19/0.47  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.19/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.47  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.19/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.19/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(abstractness_v1_pre_topc, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ( v1_pre_topc @ A ) =>
% 0.19/0.47         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_pre_topc @ X0)
% 0.19/0.47          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.19/0.47          | ~ (l1_pre_topc @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.19/0.47  thf(t104_tmap_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.19/0.47             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.47            ( l1_pre_topc @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47              ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.19/0.47                ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) =
% 0.19/0.47                  ( k5_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t104_tmap_1])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d9_tmap_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( k6_tmap_1 @ A @ B ) =
% 0.19/0.47             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.47          | ((k6_tmap_1 @ X7 @ X6)
% 0.19/0.47              = (g1_pre_topc @ (u1_struct_0 @ X7) @ (k5_tmap_1 @ X7 @ X6)))
% 0.19/0.47          | ~ (l1_pre_topc @ X7)
% 0.19/0.47          | ~ (v2_pre_topc @ X7)
% 0.19/0.47          | (v2_struct_0 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (((v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.19/0.47            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (((v2_struct_0 @ sk_A)
% 0.19/0.47        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.19/0.47            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.47  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.19/0.47         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf(dt_u1_pre_topc, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( m1_subset_1 @
% 0.19/0.47         ( u1_pre_topc @ A ) @ 
% 0.19/0.47         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X1 : $i]:
% 0.19/0.47         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.19/0.47           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.19/0.47          | ~ (l1_pre_topc @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.19/0.47  thf(free_g1_pre_topc, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.47       ( ![C:$i,D:$i]:
% 0.19/0.47         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.19/0.47           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         (((g1_pre_topc @ X4 @ X5) != (g1_pre_topc @ X2 @ X3))
% 0.19/0.47          | ((X4) = (X2))
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.19/0.47      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X0)
% 0.19/0.47          | ((u1_struct_0 @ X0) = (X1))
% 0.19/0.47          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.19/0.47              != (g1_pre_topc @ X1 @ X2)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.19/0.47            != (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47          | ((u1_struct_0 @ X0) = (u1_struct_0 @ sk_A))
% 0.19/0.47          | ~ (l1_pre_topc @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['8', '11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((X0) != (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | ~ (v1_pre_topc @ X0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | ((u1_struct_0 @ X0) = (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.19/0.47        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(dt_k6_tmap_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.47         ( l1_pre_topc @ A ) & 
% 0.19/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.47       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.19/0.47         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.19/0.47         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X8)
% 0.19/0.47          | ~ (v2_pre_topc @ X8)
% 0.19/0.47          | (v2_struct_0 @ X8)
% 0.19/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.19/0.47          | (l1_pre_topc @ (k6_tmap_1 @ X8 @ X9)))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47        | (v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.19/0.47  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('22', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('clc', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X8)
% 0.19/0.47          | ~ (v2_pre_topc @ X8)
% 0.19/0.47          | (v2_struct_0 @ X8)
% 0.19/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.19/0.47          | (v1_pre_topc @ (k6_tmap_1 @ X8 @ X9)))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47        | (v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.47  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.19/0.47  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('30', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('clc', [status(thm)], ['28', '29'])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('simplify_reflect+', [status(thm)], ['14', '22', '30'])).
% 0.19/0.47  thf('32', plain,
% 0.19/0.47      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.19/0.47        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47            != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A)))
% 0.19/0.47         <= (~
% 0.19/0.47             (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.19/0.47      inference('split', [status(esa)], ['32'])).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.19/0.47         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_pre_topc @ X0)
% 0.19/0.47          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.19/0.47          | ~ (l1_pre_topc @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.19/0.47  thf('36', plain,
% 0.19/0.47      (![X1 : $i]:
% 0.19/0.47         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.19/0.47           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.19/0.47          | ~ (l1_pre_topc @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.19/0.47  thf('37', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         (((g1_pre_topc @ X4 @ X5) != (g1_pre_topc @ X2 @ X3))
% 0.19/0.47          | ((X5) = (X3))
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.19/0.47      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.19/0.47  thf('38', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X0)
% 0.19/0.47          | ((u1_pre_topc @ X0) = (X1))
% 0.19/0.47          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.19/0.47              != (g1_pre_topc @ X2 @ X1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.47  thf('39', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | ~ (v1_pre_topc @ X0)
% 0.19/0.47          | ((u1_pre_topc @ X0) = (X1))
% 0.19/0.47          | ~ (l1_pre_topc @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['35', '38'])).
% 0.19/0.47  thf('40', plain,
% 0.19/0.47      (![X1 : $i, X2 : $i]:
% 0.19/0.47         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 0.19/0.47          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.19/0.47          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['39'])).
% 0.19/0.47  thf('41', plain,
% 0.19/0.47      ((~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47        | ~ (l1_pre_topc @ 
% 0.19/0.47             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.19/0.47        | ((u1_pre_topc @ 
% 0.19/0.47            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.19/0.47            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['34', '40'])).
% 0.19/0.47  thf('42', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('clc', [status(thm)], ['28', '29'])).
% 0.19/0.47  thf('43', plain,
% 0.19/0.47      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.19/0.47         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('44', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('clc', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('45', plain,
% 0.19/0.47      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.19/0.47         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('46', plain,
% 0.19/0.47      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.19/0.47  thf('47', plain,
% 0.19/0.47      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) != (k5_tmap_1 @ sk_A @ sk_B)))
% 0.19/0.47         <= (~
% 0.19/0.47             (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47                = (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('split', [status(esa)], ['32'])).
% 0.19/0.47  thf('48', plain,
% 0.19/0.47      ((((k5_tmap_1 @ sk_A @ sk_B) != (k5_tmap_1 @ sk_A @ sk_B)))
% 0.19/0.47         <= (~
% 0.19/0.47             (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.19/0.47                = (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.47  thf('49', plain,
% 0.19/0.47      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['48'])).
% 0.19/0.47  thf('50', plain,
% 0.19/0.47      (~ (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))) | 
% 0.19/0.47       ~
% 0.19/0.47       (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('split', [status(esa)], ['32'])).
% 0.19/0.47  thf('51', plain,
% 0.19/0.47      (~ (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.19/0.47  thf('52', plain,
% 0.19/0.47      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['33', '51'])).
% 0.19/0.47  thf('53', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['31', '52'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
