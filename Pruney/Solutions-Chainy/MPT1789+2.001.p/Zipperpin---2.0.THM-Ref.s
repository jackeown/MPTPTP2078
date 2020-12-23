%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GXxhMLQXJn

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 197 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  659 (3005 expanded)
%              Number of equality atoms :   49 ( 197 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf('0',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k5_tmap_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_tmap_1])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( k5_tmap_1 @ sk_A @ sk_B )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B )
      = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('17',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('20',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_tmap_1 @ sk_A @ sk_B )
    = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['14','17','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k6_tmap_1 @ X8 @ X7 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( k5_tmap_1 @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k5_tmap_1 @ sk_A @ sk_B )
    = ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','30'])).

thf('32',plain,
    ( $false
   <= ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('34',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('40',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('41',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
 != ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['32','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GXxhMLQXJn
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:40:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 27 iterations in 0.019s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.22/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.22/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.49  thf(t104_tmap_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.49             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.49            ( l1_pre_topc @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49              ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.49                ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) =
% 0.22/0.49                  ( k5_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t104_tmap_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.22/0.49        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.49            != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) != (k5_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.49                = (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf(abstractness_v1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ( v1_pre_topc @ A ) =>
% 0.22/0.49         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_pre_topc @ X0)
% 0.22/0.49          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k5_tmap_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.49         ( l1_pre_topc @ A ) & 
% 0.22/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49       ( m1_subset_1 @
% 0.22/0.49         ( k5_tmap_1 @ A @ B ) @ 
% 0.22/0.49         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X9)
% 0.22/0.49          | ~ (v2_pre_topc @ X9)
% 0.22/0.49          | (v2_struct_0 @ X9)
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.49          | (m1_subset_1 @ (k5_tmap_1 @ X9 @ X10) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k5_tmap_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.49         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.49        | (v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.49         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.49  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf(free_g1_pre_topc, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.49       ( ![C:$i,D:$i]:
% 0.22/0.49         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.22/0.49           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.22/0.49          | ((X6) = (X4))
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.22/0.49      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k5_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.22/0.49          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.22/0.49              != (g1_pre_topc @ X1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.22/0.49            != (X0))
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (v1_pre_topc @ X0)
% 0.22/0.49          | ((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((((k5_tmap_1 @ sk_A @ sk_B)
% 0.22/0.49          = (u1_pre_topc @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))
% 0.22/0.49        | ~ (v1_pre_topc @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.49        | ~ (l1_pre_topc @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf(dt_g1_pre_topc, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.49       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.22/0.49         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((l1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.22/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((l1_pre_topc @ 
% 0.22/0.49        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.22/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((v1_pre_topc @ 
% 0.22/0.49        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((k5_tmap_1 @ sk_A @ sk_B)
% 0.22/0.49         = (u1_pre_topc @ 
% 0.22/0.49            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('simplify_reflect+', [status(thm)], ['14', '17', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d9_tmap_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( k6_tmap_1 @ A @ B ) =
% 0.22/0.49             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.49          | ((k6_tmap_1 @ X8 @ X7)
% 0.22/0.49              = (g1_pre_topc @ (u1_struct_0 @ X8) @ (k5_tmap_1 @ X8 @ X7)))
% 0.22/0.49          | ~ (l1_pre_topc @ X8)
% 0.22/0.49          | ~ (v2_pre_topc @ X8)
% 0.22/0.49          | (v2_struct_0 @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.22/0.49            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.22/0.49            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.49  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.22/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      ((((k5_tmap_1 @ sk_A @ sk_B) != (k5_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.49                = (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (($false)
% 0.22/0.49         <= (~
% 0.22/0.49             (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.49                = (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_pre_topc @ X0)
% 0.22/0.49          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.22/0.49          | ((X5) = (X3))
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.22/0.49      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((u1_struct_0 @ sk_A) = (X0))
% 0.22/0.49          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.22/0.49              != (g1_pre_topc @ X0 @ X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.22/0.49            != (X0))
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (v1_pre_topc @ X0)
% 0.22/0.49          | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['33', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((((u1_struct_0 @ sk_A)
% 0.22/0.49          = (u1_struct_0 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))
% 0.22/0.49        | ~ (v1_pre_topc @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.49        | ~ (l1_pre_topc @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((l1_pre_topc @ 
% 0.22/0.49        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      ((v1_pre_topc @ 
% 0.22/0.49        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (((u1_struct_0 @ sk_A)
% 0.22/0.49         = (u1_struct_0 @ 
% 0.22/0.49            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('simplify_reflect+', [status(thm)], ['38', '39', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.22/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))) | 
% 0.22/0.49       ~ (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.22/0.49  thf('49', plain, ($false),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['32', '48'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
