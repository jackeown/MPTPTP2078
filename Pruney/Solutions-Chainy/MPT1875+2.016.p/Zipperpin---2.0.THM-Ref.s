%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w8O0lz2HAw

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   65 (  90 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  382 ( 689 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_tdlat_3 @ X15 )
      | ( v2_tex_2 @ X14 @ X15 )
      | ( X14
       != ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('2',plain,(
    ! [X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X15 ) @ X15 )
      | ~ ( v1_tdlat_3 @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X15 ) @ X15 )
      | ~ ( v1_tdlat_3 @ X15 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ( v2_tex_2 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w8O0lz2HAw
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 15:56:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 62 iterations in 0.033s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.23/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.23/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(t43_tex_2, conjecture,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.23/0.51         ( l1_pre_topc @ A ) ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]:
% 0.23/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.51            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.51          ( ![B:$i]:
% 0.23/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.23/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t27_tex_2, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.23/0.51             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X14 : $i, X15 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.23/0.51          | ~ (v1_tdlat_3 @ X15)
% 0.23/0.51          | (v2_tex_2 @ X14 @ X15)
% 0.23/0.51          | ((X14) != (u1_struct_0 @ X15))
% 0.23/0.51          | ~ (l1_pre_topc @ X15)
% 0.23/0.51          | (v2_struct_0 @ X15))),
% 0.23/0.51      inference('cnf', [status(esa)], [t27_tex_2])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X15 : $i]:
% 0.23/0.51         ((v2_struct_0 @ X15)
% 0.23/0.51          | ~ (l1_pre_topc @ X15)
% 0.23/0.51          | (v2_tex_2 @ (u1_struct_0 @ X15) @ X15)
% 0.23/0.51          | ~ (v1_tdlat_3 @ X15)
% 0.23/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.23/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.23/0.51  thf(dt_k2_subset_1, axiom,
% 0.23/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.23/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.51  thf('4', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.51  thf('5', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.23/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X15 : $i]:
% 0.23/0.51         ((v2_struct_0 @ X15)
% 0.23/0.51          | ~ (l1_pre_topc @ X15)
% 0.23/0.51          | (v2_tex_2 @ (u1_struct_0 @ X15) @ X15)
% 0.23/0.51          | ~ (v1_tdlat_3 @ X15))),
% 0.23/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d2_subset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X5 : $i, X6 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X5 @ X6)
% 0.23/0.51          | (r2_hidden @ X5 @ X6)
% 0.23/0.51          | (v1_xboole_0 @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.51  thf(d1_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.23/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X3 @ X2)
% 0.23/0.51          | (r1_tarski @ X3 @ X1)
% 0.23/0.51          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X1 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['9', '11'])).
% 0.23/0.51  thf('13', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.23/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X7 @ X6) | (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (v1_xboole_0 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['12', '15'])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('18', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.23/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(t28_tex_2, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( l1_pre_topc @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51           ( ![C:$i]:
% 0.23/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.23/0.51                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.23/0.51          | ~ (v2_tex_2 @ X16 @ X17)
% 0.23/0.51          | ~ (r1_tarski @ X18 @ X16)
% 0.23/0.51          | (v2_tex_2 @ X18 @ X17)
% 0.23/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.23/0.51          | ~ (l1_pre_topc @ X17))),
% 0.23/0.51      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (l1_pre_topc @ X0)
% 0.23/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.51          | (v2_tex_2 @ X1 @ X0)
% 0.23/0.51          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.23/0.51          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (v2_tex_2 @ sk_B @ sk_A)
% 0.23/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['17', '20'])).
% 0.23/0.51  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.23/0.51  thf('24', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      ((~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.23/0.51      inference('clc', [status(thm)], ['23', '24'])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '25'])).
% 0.23/0.51  thf('27', plain,
% 0.23/0.51      ((~ (v1_tdlat_3 @ sk_A)
% 0.23/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | (v2_struct_0 @ sk_A)
% 0.23/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['6', '26'])).
% 0.23/0.51  thf('28', plain, ((v1_tdlat_3 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('30', plain,
% 0.23/0.51      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.23/0.51  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('32', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.23/0.51  thf(fc2_struct_0, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.51  thf('33', plain,
% 0.23/0.51      (![X13 : $i]:
% 0.23/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.23/0.51          | ~ (l1_struct_0 @ X13)
% 0.23/0.51          | (v2_struct_0 @ X13))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.51  thf('34', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.23/0.51  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(dt_l1_pre_topc, axiom,
% 0.23/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.51  thf('36', plain,
% 0.23/0.51      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.23/0.51  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.23/0.51  thf('38', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.51      inference('demod', [status(thm)], ['34', '37'])).
% 0.23/0.51  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
