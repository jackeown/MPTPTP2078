%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8paOCFGopk

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  83 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  448 ( 861 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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

thf(rc1_connsp_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v2_tex_2 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

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

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v2_tex_2 @ X3 @ X4 )
      | ( v3_tex_2 @ ( sk_C @ X3 @ X4 ) @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v3_tdlat_3 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v2_tex_2 @ X3 @ X4 )
      | ( m1_subset_1 @ ( sk_C @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v3_tdlat_3 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X5: $i] :
      ( ~ ( v3_tex_2 @ X5 @ sk_A )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) ),
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
    | ~ ( v3_tex_2 @ ( sk_C @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( v3_tex_2 @ ( sk_C @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','28'])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8paOCFGopk
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 20 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.47  thf(t66_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.47         ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ?[B:$i]:
% 0.20/0.47         ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.47           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ?[B:$i]:
% 0.20/0.47            ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.47              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.20/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(rc1_connsp_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ?[B:$i]:
% 0.20/0.47         ( ( v1_xboole_0 @ B ) & 
% 0.20/0.47           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X0 : $i]: ((v1_xboole_0 @ (sk_B @ X0)) | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.20/0.47  thf(t35_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v1_xboole_0 @ X1)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.47          | (v2_tex_2 @ X1 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v2_struct_0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.20/0.47          | ~ (v1_xboole_0 @ (sk_B @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_xboole_0 @ (sk_B @ X0))
% 0.20/0.47          | (v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_tex_2 @ (sk_B @ X0) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.20/0.47  thf(t65_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.47         ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.47                ( ![C:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.47          | ~ (v2_tex_2 @ X3 @ X4)
% 0.20/0.47          | (v3_tex_2 @ (sk_C @ X3 @ X4) @ X4)
% 0.20/0.47          | ~ (l1_pre_topc @ X4)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X4)
% 0.20/0.47          | ~ (v2_pre_topc @ X4)
% 0.20/0.47          | (v2_struct_0 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v3_tex_2 @ (sk_C @ (sk_B @ X0) @ X0) @ X0)
% 0.20/0.47          | ~ (v2_tex_2 @ (sk_B @ X0) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.20/0.47          | (v3_tex_2 @ (sk_C @ (sk_B @ X0) @ X0) @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | (v3_tex_2 @ (sk_C @ (sk_B @ X0) @ X0) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v3_tex_2 @ (sk_C @ (sk_B @ X0) @ X0) @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.47          | ~ (v2_tex_2 @ X3 @ X4)
% 0.20/0.47          | (m1_subset_1 @ (sk_C @ X3 @ X4) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.47          | ~ (l1_pre_topc @ X4)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X4)
% 0.20/0.47          | ~ (v2_pre_topc @ X4)
% 0.20/0.47          | (v2_struct_0 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (m1_subset_1 @ (sk_C @ (sk_B @ X0) @ X0) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (v2_tex_2 @ (sk_B @ X0) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.20/0.47          | (m1_subset_1 @ (sk_C @ (sk_B @ X0) @ X0) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | (m1_subset_1 @ (sk_C @ (sk_B @ X0) @ X0) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (sk_C @ (sk_B @ X0) @ X0) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X5 : $i]:
% 0.20/0.47         (~ (v3_tex_2 @ X5 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.47        | ~ (v3_tex_2 @ (sk_C @ (sk_B @ sk_A) @ sk_A) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v3_tex_2 @ (sk_C @ (sk_B @ sk_A) @ sk_A) @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.20/0.47  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain, (~ (v3_tex_2 @ (sk_C @ (sk_B @ sk_A) @ sk_A) @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '28'])).
% 0.20/0.47  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.20/0.47  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
