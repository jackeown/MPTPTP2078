%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vgSewrV6AB

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:41 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  389 ( 864 expanded)
%              Number of equality atoms :    5 (  20 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(t66_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ? [B: $i] :
            ( ( v3_tex_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v2_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( v3_tex_2 @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( ~ ( v3_tex_2 @ X12 @ sk_A )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vgSewrV6AB
% 0.11/0.30  % Computer   : n017.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 19:50:17 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  % Running portfolio for 600 s
% 0.11/0.30  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.30  % Number of cores: 8
% 0.11/0.31  % Python version: Python 3.6.8
% 0.11/0.31  % Running in FO mode
% 0.16/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.16/0.43  % Solved by: fo/fo7.sh
% 0.16/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.43  % done 28 iterations in 0.019s
% 0.16/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.16/0.43  % SZS output start Refutation
% 0.16/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.16/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.16/0.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.16/0.43  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.16/0.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.16/0.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.16/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.16/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.16/0.43  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.16/0.43  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.16/0.43  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.16/0.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.16/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.16/0.43  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.16/0.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.16/0.43  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.16/0.43  thf(t66_tex_2, conjecture,
% 0.16/0.43    (![A:$i]:
% 0.16/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.16/0.43         ( l1_pre_topc @ A ) ) =>
% 0.16/0.43       ( ?[B:$i]:
% 0.16/0.43         ( ( v3_tex_2 @ B @ A ) & 
% 0.16/0.43           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.16/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.43    (~( ![A:$i]:
% 0.16/0.43        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.16/0.43            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.16/0.43          ( ?[B:$i]:
% 0.16/0.43            ( ( v3_tex_2 @ B @ A ) & 
% 0.16/0.43              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.16/0.43    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.16/0.43  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf(t46_xboole_1, axiom,
% 0.16/0.43    (![A:$i,B:$i]:
% 0.16/0.43     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.16/0.43  thf('1', plain,
% 0.16/0.43      (![X2 : $i, X3 : $i]:
% 0.16/0.43         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (k1_xboole_0))),
% 0.16/0.43      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.16/0.43  thf(redefinition_k6_subset_1, axiom,
% 0.16/0.43    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.16/0.43  thf('2', plain,
% 0.16/0.43      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.16/0.43      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.16/0.43  thf('3', plain,
% 0.16/0.43      (![X2 : $i, X3 : $i]:
% 0.16/0.43         ((k6_subset_1 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (k1_xboole_0))),
% 0.16/0.43      inference('demod', [status(thm)], ['1', '2'])).
% 0.16/0.43  thf(dt_k6_subset_1, axiom,
% 0.16/0.43    (![A:$i,B:$i]:
% 0.16/0.43     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.16/0.43  thf('4', plain,
% 0.16/0.43      (![X4 : $i, X5 : $i]:
% 0.16/0.43         (m1_subset_1 @ (k6_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))),
% 0.16/0.43      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.16/0.43  thf('5', plain,
% 0.16/0.43      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.16/0.43      inference('sup+', [status(thm)], ['3', '4'])).
% 0.16/0.43  thf(t35_tex_2, axiom,
% 0.16/0.43    (![A:$i]:
% 0.16/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.16/0.43       ( ![B:$i]:
% 0.16/0.43         ( ( ( v1_xboole_0 @ B ) & 
% 0.16/0.43             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.16/0.43           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.16/0.43  thf('6', plain,
% 0.16/0.43      (![X8 : $i, X9 : $i]:
% 0.16/0.43         (~ (v1_xboole_0 @ X8)
% 0.16/0.43          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.16/0.43          | (v2_tex_2 @ X8 @ X9)
% 0.16/0.43          | ~ (l1_pre_topc @ X9)
% 0.16/0.43          | ~ (v2_pre_topc @ X9)
% 0.16/0.43          | (v2_struct_0 @ X9))),
% 0.16/0.43      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.16/0.43  thf('7', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         ((v2_struct_0 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | ~ (l1_pre_topc @ X0)
% 0.16/0.43          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.16/0.43          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.16/0.43      inference('sup-', [status(thm)], ['5', '6'])).
% 0.16/0.43  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.16/0.43  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.16/0.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.16/0.43  thf('9', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         ((v2_struct_0 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | ~ (l1_pre_topc @ X0)
% 0.16/0.43          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.16/0.43      inference('demod', [status(thm)], ['7', '8'])).
% 0.16/0.43  thf('10', plain,
% 0.16/0.43      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.16/0.43      inference('sup+', [status(thm)], ['3', '4'])).
% 0.16/0.43  thf(t65_tex_2, axiom,
% 0.16/0.43    (![A:$i]:
% 0.16/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.16/0.43         ( l1_pre_topc @ A ) ) =>
% 0.16/0.43       ( ![B:$i]:
% 0.16/0.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.43           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.16/0.43                ( ![C:$i]:
% 0.16/0.43                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.43                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.16/0.43  thf('11', plain,
% 0.16/0.43      (![X10 : $i, X11 : $i]:
% 0.16/0.43         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.16/0.43          | ~ (v2_tex_2 @ X10 @ X11)
% 0.16/0.43          | (v3_tex_2 @ (sk_C @ X10 @ X11) @ X11)
% 0.16/0.43          | ~ (l1_pre_topc @ X11)
% 0.16/0.43          | ~ (v3_tdlat_3 @ X11)
% 0.16/0.43          | ~ (v2_pre_topc @ X11)
% 0.16/0.43          | (v2_struct_0 @ X11))),
% 0.16/0.43      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.16/0.43  thf('12', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         ((v2_struct_0 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | ~ (v3_tdlat_3 @ X0)
% 0.16/0.43          | ~ (l1_pre_topc @ X0)
% 0.16/0.43          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.16/0.43          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.16/0.43      inference('sup-', [status(thm)], ['10', '11'])).
% 0.16/0.43  thf('13', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         (~ (l1_pre_topc @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | (v2_struct_0 @ X0)
% 0.16/0.43          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.16/0.43          | ~ (l1_pre_topc @ X0)
% 0.16/0.43          | ~ (v3_tdlat_3 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | (v2_struct_0 @ X0))),
% 0.16/0.43      inference('sup-', [status(thm)], ['9', '12'])).
% 0.16/0.43  thf('14', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         (~ (v3_tdlat_3 @ X0)
% 0.16/0.43          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.16/0.43          | (v2_struct_0 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | ~ (l1_pre_topc @ X0))),
% 0.16/0.43      inference('simplify', [status(thm)], ['13'])).
% 0.16/0.43  thf('15', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         ((v2_struct_0 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | ~ (l1_pre_topc @ X0)
% 0.16/0.43          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.16/0.43      inference('demod', [status(thm)], ['7', '8'])).
% 0.16/0.43  thf('16', plain,
% 0.16/0.43      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.16/0.43      inference('sup+', [status(thm)], ['3', '4'])).
% 0.16/0.43  thf('17', plain,
% 0.16/0.43      (![X10 : $i, X11 : $i]:
% 0.16/0.43         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.16/0.43          | ~ (v2_tex_2 @ X10 @ X11)
% 0.16/0.43          | (m1_subset_1 @ (sk_C @ X10 @ X11) @ 
% 0.16/0.43             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.16/0.43          | ~ (l1_pre_topc @ X11)
% 0.16/0.43          | ~ (v3_tdlat_3 @ X11)
% 0.16/0.43          | ~ (v2_pre_topc @ X11)
% 0.16/0.43          | (v2_struct_0 @ X11))),
% 0.16/0.43      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.16/0.43  thf('18', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         ((v2_struct_0 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | ~ (v3_tdlat_3 @ X0)
% 0.16/0.43          | ~ (l1_pre_topc @ X0)
% 0.16/0.43          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.16/0.43             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.16/0.43          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.16/0.43      inference('sup-', [status(thm)], ['16', '17'])).
% 0.16/0.43  thf('19', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         (~ (l1_pre_topc @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | (v2_struct_0 @ X0)
% 0.16/0.43          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.16/0.43             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.16/0.43          | ~ (l1_pre_topc @ X0)
% 0.16/0.43          | ~ (v3_tdlat_3 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | (v2_struct_0 @ X0))),
% 0.16/0.43      inference('sup-', [status(thm)], ['15', '18'])).
% 0.16/0.43  thf('20', plain,
% 0.16/0.43      (![X0 : $i]:
% 0.16/0.43         (~ (v3_tdlat_3 @ X0)
% 0.16/0.43          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.16/0.43             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.16/0.43          | (v2_struct_0 @ X0)
% 0.16/0.43          | ~ (v2_pre_topc @ X0)
% 0.16/0.43          | ~ (l1_pre_topc @ X0))),
% 0.16/0.43      inference('simplify', [status(thm)], ['19'])).
% 0.16/0.43  thf('21', plain,
% 0.16/0.43      (![X12 : $i]:
% 0.16/0.43         (~ (v3_tex_2 @ X12 @ sk_A)
% 0.16/0.43          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf('22', plain,
% 0.16/0.43      ((~ (l1_pre_topc @ sk_A)
% 0.16/0.43        | ~ (v2_pre_topc @ sk_A)
% 0.16/0.43        | (v2_struct_0 @ sk_A)
% 0.16/0.43        | ~ (v3_tdlat_3 @ sk_A)
% 0.16/0.43        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.16/0.43      inference('sup-', [status(thm)], ['20', '21'])).
% 0.16/0.43  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf('25', plain, ((v3_tdlat_3 @ sk_A)),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf('26', plain,
% 0.16/0.43      (((v2_struct_0 @ sk_A)
% 0.16/0.43        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.16/0.43      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.16/0.43  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf('28', plain, (~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.16/0.43      inference('clc', [status(thm)], ['26', '27'])).
% 0.16/0.43  thf('29', plain,
% 0.16/0.43      ((~ (l1_pre_topc @ sk_A)
% 0.16/0.43        | ~ (v2_pre_topc @ sk_A)
% 0.16/0.43        | (v2_struct_0 @ sk_A)
% 0.16/0.43        | ~ (v3_tdlat_3 @ sk_A))),
% 0.16/0.43      inference('sup-', [status(thm)], ['14', '28'])).
% 0.16/0.43  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf('33', plain, ((v2_struct_0 @ sk_A)),
% 0.16/0.43      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.16/0.43  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.16/0.43  
% 0.16/0.43  % SZS output end Refutation
% 0.16/0.43  
% 0.16/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
