%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhTvfhdd0s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 ( 969 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_0_tex_2_type,type,(
    a_2_0_tex_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t63_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
           => ( ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
             => ( ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) )
                = ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_tex_2])).

thf('1',plain,(
    ( k3_tarski @ ( a_2_0_tex_2 @ sk_A @ sk_B ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = ( k3_tarski @ ( a_2_0_tex_2 @ X5 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v3_tdlat_3 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t54_tex_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k3_tarski @ ( a_2_0_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v1_tops_1 @ X2 @ X3 )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = ( k2_struct_0 @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_tops_1 @ X6 @ X7 )
      | ~ ( v3_tex_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v3_tdlat_3 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t62_tex_2])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
      = ( k3_tarski @ ( a_2_0_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k3_tarski @ ( a_2_0_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ( k2_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('30',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhTvfhdd0s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 24 iterations in 0.015s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.47  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(a_2_0_tex_2_type, type, a_2_0_tex_2: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(d3_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.47  thf(t63_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.47         ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v3_tex_2 @ B @ A ) =>
% 0.20/0.47             ( ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47              ( ( v3_tex_2 @ B @ A ) =>
% 0.20/0.47                ( ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) ) = ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t63_tex_2])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (((k3_tarski @ (a_2_0_tex_2 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t54_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.47         ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( k2_pre_topc @ A @ B ) = ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) ) ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.47          | ((k2_pre_topc @ X5 @ X4) = (k3_tarski @ (a_2_0_tex_2 @ X5 @ X4)))
% 0.20/0.47          | ~ (l1_pre_topc @ X5)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X5)
% 0.20/0.47          | ~ (v2_pre_topc @ X5)
% 0.20/0.47          | (v2_struct_0 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t54_tex_2])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.47            = (k3_tarski @ (a_2_0_tex_2 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d3_tops_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.47             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.47          | ~ (v1_tops_1 @ X2 @ X3)
% 0.20/0.47          | ((k2_pre_topc @ X3 @ X2) = (k2_struct_0 @ X3))
% 0.20/0.47          | ~ (l1_pre_topc @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.20/0.47        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.20/0.47        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t62_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.47         ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v3_tex_2 @ B @ A ) => ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.47          | (v1_tops_1 @ X6 @ X7)
% 0.20/0.47          | ~ (v3_tex_2 @ X6 @ X7)
% 0.20/0.47          | ~ (l1_pre_topc @ X7)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X7)
% 0.20/0.47          | ~ (v2_pre_topc @ X7)
% 0.20/0.47          | (v2_struct_0 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t62_tex_2])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ~ (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.47        | (v1_tops_1 @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, (((v2_struct_0 @ sk_A) | (v1_tops_1 @ sk_B @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.20/0.47  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((k2_struct_0 @ sk_A) = (k3_tarski @ (a_2_0_tex_2 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5', '6', '7', '23'])).
% 0.20/0.47  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((k2_struct_0 @ sk_A) = (k3_tarski @ (a_2_0_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain, (((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['1', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '27'])).
% 0.20/0.47  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_l1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.47  thf('30', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.47  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '31'])).
% 0.20/0.47  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
