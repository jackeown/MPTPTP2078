%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z8vrfALZuE

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 111 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  416 ( 852 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v2_tex_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(rc11_pre_topc,axiom,(
    ? [A: $i] :
      ( ( v1_pre_topc @ A )
      & ( v2_struct_0 @ A )
      & ( l1_pre_topc @ A ) ) )).

thf('4',plain,(
    v2_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc11_pre_topc])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[rc11_pre_topc])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( v3_tex_2 @ ( sk_C @ X11 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( ~ ( v3_tex_2 @ X13 @ sk_A_1 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v2_pre_topc @ sk_A_1 )
    | ( v2_struct_0 @ sk_A_1 )
    | ~ ( v3_tdlat_3 @ sk_A_1 )
    | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A_1 ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_tdlat_3 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A_1 )
    | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A_1 ) @ sk_A_1 ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A_1 ) @ sk_A_1 ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v2_pre_topc @ sk_A_1 )
    | ( v2_struct_0 @ sk_A_1 )
    | ~ ( v3_tdlat_3 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['20','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_tdlat_3 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_struct_0 @ sk_A_1 ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z8vrfALZuE
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:15:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 39 iterations in 0.023s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.47  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(t66_tex_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.47         ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ?[B:$i]:
% 0.21/0.47         ( ( v3_tex_2 @ B @ A ) & 
% 0.21/0.47           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ?[B:$i]:
% 0.21/0.47            ( ( v3_tex_2 @ B @ A ) & 
% 0.21/0.47              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.21/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t4_subset_1, axiom,
% 0.21/0.47    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.47  thf(t35_tex_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X9)
% 0.21/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.47          | (v2_tex_2 @ X9 @ X10)
% 0.21/0.47          | ~ (l1_pre_topc @ X10)
% 0.21/0.47          | ~ (v2_pre_topc @ X10)
% 0.21/0.47          | (v2_struct_0 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v2_pre_topc @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0)
% 0.21/0.47          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.47          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(rc11_pre_topc, axiom,
% 0.21/0.47    (?[A:$i]:
% 0.21/0.47     ( ( v1_pre_topc @ A ) & ( v2_struct_0 @ A ) & ( l1_pre_topc @ A ) ))).
% 0.21/0.48  thf('4', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [rc11_pre_topc])).
% 0.21/0.48  thf(fc1_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (l1_struct_0 @ X8)
% 0.21/0.48          | ~ (v2_struct_0 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.48  thf(cc4_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.48           ( v1_xboole_0 @ C ) ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ X4)
% 0.21/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.48          | (v1_xboole_0 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (l1_struct_0 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.48  thf('10', plain, (((v1_xboole_0 @ k1_xboole_0) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.48  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [rc11_pre_topc])).
% 0.21/0.48  thf(dt_l1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('12', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X0)
% 0.21/0.48          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.48  thf(t65_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.48                ( ![C:$i]:
% 0.21/0.48                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.48          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.48          | (v3_tex_2 @ (sk_C @ X11 @ X12) @ X12)
% 0.21/0.48          | ~ (l1_pre_topc @ X12)
% 0.21/0.48          | ~ (v3_tdlat_3 @ X12)
% 0.21/0.48          | ~ (v2_pre_topc @ X12)
% 0.21/0.48          | (v2_struct_0 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X0)
% 0.21/0.48          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.48          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X0)
% 0.21/0.48          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v3_tdlat_3 @ X0)
% 0.21/0.48          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X0)
% 0.21/0.48          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '14'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.48          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.48          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.48          | ~ (l1_pre_topc @ X12)
% 0.21/0.48          | ~ (v3_tdlat_3 @ X12)
% 0.21/0.48          | ~ (v2_pre_topc @ X12)
% 0.21/0.48          | (v2_struct_0 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X0)
% 0.21/0.48          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.48          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.48          | ~ (l1_pre_topc @ X0)
% 0.21/0.48          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v3_tdlat_3 @ X0)
% 0.21/0.48          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v2_pre_topc @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X13 : $i]:
% 0.21/0.48         (~ (v3_tex_2 @ X13 @ sk_A_1)
% 0.21/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A_1))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A_1)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A_1)
% 0.21/0.48        | (v2_struct_0 @ sk_A_1)
% 0.21/0.48        | ~ (v3_tdlat_3 @ sk_A_1)
% 0.21/0.48        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A_1) @ sk_A_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain, ((l1_pre_topc @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, ((v2_pre_topc @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, ((v3_tdlat_3 @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A_1)
% 0.21/0.48        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A_1) @ sk_A_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.48  thf('33', plain, (~ (v2_struct_0 @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain, (~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A_1) @ sk_A_1)),
% 0.21/0.48      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A_1)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A_1)
% 0.21/0.48        | (v2_struct_0 @ sk_A_1)
% 0.21/0.48        | ~ (v3_tdlat_3 @ sk_A_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '34'])).
% 0.21/0.48  thf('36', plain, ((l1_pre_topc @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('37', plain, ((v2_pre_topc @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain, ((v3_tdlat_3 @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain, ((v2_struct_0 @ sk_A_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.21/0.48  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
