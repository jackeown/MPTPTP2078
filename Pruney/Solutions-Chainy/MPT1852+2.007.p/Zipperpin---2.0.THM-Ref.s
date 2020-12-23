%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AohfJiXXe5

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 113 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  441 (1312 expanded)
%              Number of equality atoms :   27 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t19_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v3_tdlat_3 @ A ) )
           => ( v3_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v3_tdlat_3 @ A ) )
             => ( v3_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_tex_2])).

thf('0',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_pre_topc @ X3 @ X4 )
       != ( g1_pre_topc @ X1 @ X2 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_1 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( u1_pre_topc @ sk_B_1 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf(d3_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
             => ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X5 ) @ ( sk_B @ X5 ) ) @ ( u1_pre_topc @ X5 ) )
      | ( v3_tdlat_3 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('9',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_pre_topc @ X3 @ X4 )
       != ( g1_pre_topc @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = X1 )
      | ~ ( l1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','21'])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_tdlat_3 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_tdlat_3 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( u1_pre_topc @ X5 ) )
      | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X5 ) @ X6 ) @ ( u1_pre_topc @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( u1_pre_topc @ sk_B_1 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('34',plain,(
    ! [X5: $i] :
      ( ( r2_hidden @ ( sk_B @ X5 ) @ ( u1_pre_topc @ X5 ) )
      | ( v3_tdlat_3 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['22','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AohfJiXXe5
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 26 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.47  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(t19_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( l1_pre_topc @ B ) =>
% 0.20/0.47           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.47                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.47               ( v3_tdlat_3 @ A ) ) =>
% 0.20/0.47             ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( l1_pre_topc @ A ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( l1_pre_topc @ B ) =>
% 0.20/0.47              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.47                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.47                  ( v3_tdlat_3 @ A ) ) =>
% 0.20/0.47                ( v3_tdlat_3 @ B ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t19_tex_2])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.47         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_u1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( m1_subset_1 @
% 0.20/0.47         ( u1_pre_topc @ A ) @ 
% 0.20/0.47         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.47  thf(free_g1_pre_topc, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.47       ( ![C:$i,D:$i]:
% 0.20/0.47         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.20/0.47           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (((g1_pre_topc @ X3 @ X4) != (g1_pre_topc @ X1 @ X2))
% 0.20/0.47          | ((X4) = (X2))
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.20/0.47      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ((u1_pre_topc @ X0) = (X1))
% 0.20/0.47          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.47              != (g1_pre_topc @ X2 @ X1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.47            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.47          | ((u1_pre_topc @ sk_B_1) = (X0))
% 0.20/0.47          | ~ (l1_pre_topc @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.47  thf('5', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.47            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.47          | ((u1_pre_topc @ sk_B_1) = (X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, (((u1_pre_topc @ sk_B_1) = (u1_pre_topc @ sk_A))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['6'])).
% 0.20/0.47  thf(d3_tdlat_3, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.47         ( ![B:$i]:
% 0.20/0.47           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47             ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.47               ( r2_hidden @
% 0.20/0.47                 ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.47                 ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X5 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X5) @ (sk_B @ X5)) @ 
% 0.20/0.47             (u1_pre_topc @ X5))
% 0.20/0.47          | (v3_tdlat_3 @ X5)
% 0.20/0.47          | ~ (l1_pre_topc @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((~ (r2_hidden @ 
% 0.20/0.47           (k6_subset_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.47           (u1_pre_topc @ sk_A))
% 0.20/0.47        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.47        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((~ (r2_hidden @ 
% 0.20/0.47           (k6_subset_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.47           (u1_pre_topc @ sk_A))
% 0.20/0.47        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (~ (r2_hidden @ 
% 0.20/0.47          (k6_subset_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.47          (u1_pre_topc @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.47         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (((g1_pre_topc @ X3 @ X4) != (g1_pre_topc @ X1 @ X2))
% 0.20/0.47          | ((X3) = (X1))
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.20/0.47      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.47          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.47              != (g1_pre_topc @ X1 @ X2)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.47            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.47          | ((u1_struct_0 @ sk_B_1) = (X1))
% 0.20/0.47          | ~ (l1_pre_topc @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.47  thf('19', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.47            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.47          | ((u1_struct_0 @ sk_B_1) = (X1)))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.47          (u1_pre_topc @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '21'])).
% 0.20/0.47  thf('23', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['20'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X5 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.47          | (v3_tdlat_3 @ X5)
% 0.20/0.47          | ~ (l1_pre_topc @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.47        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.47        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.47        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (~ (v3_tdlat_3 @ X5)
% 0.20/0.47          | ~ (r2_hidden @ X6 @ (u1_pre_topc @ X5))
% 0.20/0.47          | (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X5) @ X6) @ 
% 0.20/0.47             (u1_pre_topc @ X5))
% 0.20/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.47          | ~ (l1_pre_topc @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (r2_hidden @ 
% 0.20/0.47           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.47           (u1_pre_topc @ sk_A))
% 0.20/0.47        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.47        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, (((u1_pre_topc @ sk_B_1) = (u1_pre_topc @ sk_A))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['6'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X5 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_B @ X5) @ (u1_pre_topc @ X5))
% 0.20/0.47          | (v3_tdlat_3 @ X5)
% 0.20/0.47          | ~ (l1_pre_topc @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.47        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.47        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.47        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('39', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.47        (u1_pre_topc @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['31', '32', '39', '40'])).
% 0.20/0.47  thf('42', plain, ($false), inference('demod', [status(thm)], ['22', '41'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
