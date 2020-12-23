%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pb0IO9vgX6

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:44 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   58 (  98 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  374 (1326 expanded)
%              Number of equality atoms :   11 (  49 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t105_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) )
             => ( ( C = B )
               => ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) )
               => ( ( C = B )
                 => ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t105_tmap_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
    | ( v3_pre_topc @ sk_C @ ( k6_tmap_1 @ sk_A @ sk_C ) )
    | ~ ( r2_hidden @ sk_C @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_C = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('9',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v3_pre_topc @ sk_C @ ( k6_tmap_1 @ sk_A @ sk_C ) )
    | ~ ( r2_hidden @ sk_C @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','14'])).

thf('16',plain,(
    ~ ( v3_pre_topc @ sk_C @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_C = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ( v3_pre_topc @ sk_C @ ( k6_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_C @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t104_tmap_1,axiom,(
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

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X7 @ X6 ) )
        = ( k5_tmap_1 @ X7 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
      = ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
      = ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
    = ( k5_tmap_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t102_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r2_hidden @ X4 @ ( k5_tmap_1 @ X5 @ X4 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_C @ ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ sk_C @ ( k5_tmap_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['19','27','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pb0IO9vgX6
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:56:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 43 iterations in 0.027s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.36/0.55  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(t105_tmap_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_subset_1 @
% 0.36/0.55                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 0.36/0.55               ( ( ( C ) = ( B ) ) =>
% 0.36/0.55                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( m1_subset_1 @
% 0.36/0.55                    C @ 
% 0.36/0.55                    ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 0.36/0.55                  ( ( ( C ) = ( B ) ) =>
% 0.36/0.55                    ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t105_tmap_1])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain, (((sk_C) = (sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_C))))),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf(d5_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.36/0.55             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.36/0.55          | (v3_pre_topc @ X0 @ X1)
% 0.36/0.55          | ~ (l1_pre_topc @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.36/0.55        | (v3_pre_topc @ sk_C @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.36/0.55        | ~ (r2_hidden @ sk_C @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain, (((sk_C) = (sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf(dt_k6_tmap_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55         ( l1_pre_topc @ A ) & 
% 0.36/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.36/0.55         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.36/0.55         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X2)
% 0.36/0.55          | ~ (v2_pre_topc @ X2)
% 0.36/0.55          | (v2_struct_0 @ X2)
% 0.36/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.36/0.55          | (l1_pre_topc @ (k6_tmap_1 @ X2 @ X3)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.36/0.55  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('14', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))),
% 0.36/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (((v3_pre_topc @ sk_C @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.36/0.55        | ~ (r2_hidden @ sk_C @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))))),
% 0.36/0.55      inference('demod', [status(thm)], ['4', '14'])).
% 0.36/0.55  thf('16', plain, (~ (v3_pre_topc @ sk_C @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('17', plain, (((sk_C) = (sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('18', plain, (~ (v3_pre_topc @ sk_C @ (k6_tmap_1 @ sk_A @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (~ (r2_hidden @ sk_C @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['15', '18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf(t104_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.36/0.55             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.36/0.55          | ((u1_pre_topc @ (k6_tmap_1 @ X7 @ X6)) = (k5_tmap_1 @ X7 @ X6))
% 0.36/0.55          | ~ (l1_pre_topc @ X7)
% 0.36/0.55          | ~ (v2_pre_topc @ X7)
% 0.36/0.55          | (v2_struct_0 @ X7))),
% 0.36/0.55      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.36/0.55            = (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.55  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.36/0.55            = (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.36/0.55  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C)) = (k5_tmap_1 @ sk_A @ sk_C))),
% 0.36/0.55      inference('clc', [status(thm)], ['25', '26'])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf(t102_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.36/0.55          | (r2_hidden @ X4 @ (k5_tmap_1 @ X5 @ X4))
% 0.36/0.55          | ~ (l1_pre_topc @ X5)
% 0.36/0.55          | ~ (v2_pre_topc @ X5)
% 0.36/0.55          | (v2_struct_0 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (r2_hidden @ sk_C @ (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_C @ (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.36/0.55  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('35', plain, ((r2_hidden @ sk_C @ (k5_tmap_1 @ sk_A @ sk_C))),
% 0.36/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf('36', plain, ($false),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '27', '35'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.41/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
