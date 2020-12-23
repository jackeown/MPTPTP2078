%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3GFSB14mIX

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 ( 758 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( v3_tex_2 @ ( sk_C @ X12 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    inference(demod,[status(thm)],['3','8'])).

thf('16',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X14: $i] :
      ( ~ ( v3_tex_2 @ X14 @ sk_A )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3GFSB14mIX
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:40:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 25 iterations in 0.018s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.48  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(t66_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ?[B:$i]:
% 0.21/0.48         ( ( v3_tex_2 @ B @ A ) & 
% 0.21/0.48           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ?[B:$i]:
% 0.21/0.48            ( ( v3_tex_2 @ B @ A ) & 
% 0.21/0.48              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.21/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t4_subset_1, axiom,
% 0.21/0.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.48  thf(t35_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.48          | (v2_tex_2 @ X10 @ X11)
% 0.21/0.48          | ~ (l1_pre_topc @ X11)
% 0.21/0.48          | ~ (v2_pre_topc @ X11)
% 0.21/0.48          | (v2_struct_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X0)
% 0.21/0.48          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('4', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf(t7_ordinal1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.49  thf(t65_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.49         ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.49                ( ![C:$i]:
% 0.21/0.49                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | ~ (v2_tex_2 @ X12 @ X13)
% 0.21/0.49          | (v3_tex_2 @ (sk_C @ X12 @ X13) @ X13)
% 0.21/0.49          | ~ (l1_pre_topc @ X13)
% 0.21/0.49          | ~ (v3_tdlat_3 @ X13)
% 0.21/0.49          | ~ (v2_pre_topc @ X13)
% 0.21/0.49          | (v2_struct_0 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.49          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | (v2_struct_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v3_tdlat_3 @ X0)
% 0.21/0.49          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | ~ (v2_tex_2 @ X12 @ X13)
% 0.21/0.49          | (m1_subset_1 @ (sk_C @ X12 @ X13) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | ~ (l1_pre_topc @ X13)
% 0.21/0.49          | ~ (v3_tdlat_3 @ X13)
% 0.21/0.49          | ~ (v2_pre_topc @ X13)
% 0.21/0.49          | (v2_struct_0 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | (v2_struct_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v3_tdlat_3 @ X0)
% 0.21/0.49          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X14 : $i]:
% 0.21/0.49         (~ (v3_tex_2 @ X14 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.49        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.21/0.49  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain, (~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '28'])).
% 0.21/0.49  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.21/0.49  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
