%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Ks512S6I5

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   64 (  94 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  512 ( 930 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X6 ) @ X5 ) @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ X3 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( v3_tex_2 @ ( sk_C @ X7 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v3_tdlat_3 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v3_tdlat_3 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X9: $i] :
      ( ~ ( v3_tex_2 @ X9 @ sk_A )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v3_tex_2 @ ( sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

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
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
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
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
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
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Ks512S6I5
% 0.15/0.38  % Computer   : n022.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:59:11 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 40 iterations in 0.042s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.24/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.24/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.53  thf(t66_tex_2, conjecture,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.24/0.53         ( l1_pre_topc @ A ) ) =>
% 0.24/0.53       ( ?[B:$i]:
% 0.24/0.53         ( ( v3_tex_2 @ B @ A ) & 
% 0.24/0.53           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i]:
% 0.24/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.53            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.53          ( ?[B:$i]:
% 0.24/0.53            ( ( v3_tex_2 @ B @ A ) & 
% 0.24/0.53              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.24/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(existence_m1_subset_1, axiom,
% 0.24/0.53    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.24/0.53  thf('1', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.24/0.53      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.24/0.53  thf(t36_tex_2, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.53           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (![X5 : $i, X6 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.24/0.53          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X6) @ X5) @ X6)
% 0.24/0.53          | ~ (l1_pre_topc @ X6)
% 0.24/0.53          | ~ (v2_pre_topc @ X6)
% 0.24/0.53          | (v2_struct_0 @ X6))),
% 0.24/0.53      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((v2_struct_0 @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | ~ (l1_pre_topc @ X0)
% 0.24/0.53          | (v2_tex_2 @ 
% 0.24/0.53             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53             X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.53  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.24/0.53      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.24/0.53  thf(dt_k6_domain_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X3 : $i, X4 : $i]:
% 0.24/0.53         ((v1_xboole_0 @ X3)
% 0.24/0.53          | ~ (m1_subset_1 @ X4 @ X3)
% 0.24/0.53          | (m1_subset_1 @ (k6_domain_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3)))),
% 0.24/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.24/0.53          | (v1_xboole_0 @ X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.53  thf(t65_tex_2, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.24/0.53         ( l1_pre_topc @ A ) ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.24/0.53                ( ![C:$i]:
% 0.24/0.53                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      (![X7 : $i, X8 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.24/0.53          | ~ (v2_tex_2 @ X7 @ X8)
% 0.24/0.53          | (v3_tex_2 @ (sk_C @ X7 @ X8) @ X8)
% 0.24/0.53          | ~ (l1_pre_topc @ X8)
% 0.24/0.53          | ~ (v3_tdlat_3 @ X8)
% 0.24/0.53          | ~ (v2_pre_topc @ X8)
% 0.24/0.53          | (v2_struct_0 @ X8))),
% 0.24/0.53      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.24/0.53          | (v2_struct_0 @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | ~ (v3_tdlat_3 @ X0)
% 0.24/0.53          | ~ (l1_pre_topc @ X0)
% 0.24/0.53          | (v3_tex_2 @ 
% 0.24/0.53             (sk_C @ 
% 0.24/0.53              (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53              X0) @ 
% 0.24/0.53             X0)
% 0.24/0.53          | ~ (v2_tex_2 @ 
% 0.24/0.53               (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53               X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.53  thf('9', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (l1_pre_topc @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | (v2_struct_0 @ X0)
% 0.24/0.53          | (v3_tex_2 @ 
% 0.24/0.53             (sk_C @ 
% 0.24/0.53              (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53              X0) @ 
% 0.24/0.53             X0)
% 0.24/0.53          | ~ (l1_pre_topc @ X0)
% 0.24/0.53          | ~ (v3_tdlat_3 @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | (v2_struct_0 @ X0)
% 0.24/0.53          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['3', '8'])).
% 0.24/0.53  thf('10', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.24/0.53          | ~ (v3_tdlat_3 @ X0)
% 0.24/0.53          | (v3_tex_2 @ 
% 0.24/0.53             (sk_C @ 
% 0.24/0.53              (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53              X0) @ 
% 0.24/0.53             X0)
% 0.24/0.53          | (v2_struct_0 @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | ~ (l1_pre_topc @ X0))),
% 0.24/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((v2_struct_0 @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | ~ (l1_pre_topc @ X0)
% 0.24/0.53          | (v2_tex_2 @ 
% 0.24/0.53             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53             X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.24/0.53          | (v1_xboole_0 @ X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X7 : $i, X8 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.24/0.53          | ~ (v2_tex_2 @ X7 @ X8)
% 0.24/0.53          | (m1_subset_1 @ (sk_C @ X7 @ X8) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.24/0.53          | ~ (l1_pre_topc @ X8)
% 0.24/0.53          | ~ (v3_tdlat_3 @ X8)
% 0.24/0.53          | ~ (v2_pre_topc @ X8)
% 0.24/0.53          | (v2_struct_0 @ X8))),
% 0.24/0.53      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.24/0.53          | (v2_struct_0 @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | ~ (v3_tdlat_3 @ X0)
% 0.24/0.53          | ~ (l1_pre_topc @ X0)
% 0.24/0.53          | (m1_subset_1 @ 
% 0.24/0.53             (sk_C @ 
% 0.24/0.53              (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53              X0) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.24/0.53          | ~ (v2_tex_2 @ 
% 0.24/0.53               (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53               X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (l1_pre_topc @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | (v2_struct_0 @ X0)
% 0.24/0.53          | (m1_subset_1 @ 
% 0.24/0.53             (sk_C @ 
% 0.24/0.53              (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53              X0) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.24/0.53          | ~ (l1_pre_topc @ X0)
% 0.24/0.53          | ~ (v3_tdlat_3 @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | (v2_struct_0 @ X0)
% 0.24/0.53          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['11', '14'])).
% 0.24/0.53  thf('16', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.24/0.53          | ~ (v3_tdlat_3 @ X0)
% 0.24/0.53          | (m1_subset_1 @ 
% 0.24/0.53             (sk_C @ 
% 0.24/0.53              (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.24/0.53              X0) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.24/0.53          | (v2_struct_0 @ X0)
% 0.24/0.53          | ~ (v2_pre_topc @ X0)
% 0.24/0.53          | ~ (l1_pre_topc @ X0))),
% 0.24/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      (![X9 : $i]:
% 0.24/0.53         (~ (v3_tex_2 @ X9 @ sk_A)
% 0.24/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.53        | (v2_struct_0 @ sk_A)
% 0.24/0.53        | ~ (v3_tdlat_3 @ sk_A)
% 0.24/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.53        | ~ (v3_tex_2 @ 
% 0.24/0.53             (sk_C @ 
% 0.24/0.53              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.53               (sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.24/0.53              sk_A) @ 
% 0.24/0.53             sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.53  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('21', plain, ((v3_tdlat_3 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      (((v2_struct_0 @ sk_A)
% 0.24/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.53        | ~ (v3_tex_2 @ 
% 0.24/0.53             (sk_C @ 
% 0.24/0.53              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.53               (sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.24/0.53              sk_A) @ 
% 0.24/0.53             sk_A))),
% 0.24/0.53      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.24/0.53  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      ((~ (v3_tex_2 @ 
% 0.24/0.53           (sk_C @ 
% 0.24/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.24/0.53            sk_A) @ 
% 0.24/0.53           sk_A)
% 0.24/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.24/0.53  thf('25', plain,
% 0.24/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.53        | (v2_struct_0 @ sk_A)
% 0.24/0.53        | ~ (v3_tdlat_3 @ sk_A)
% 0.24/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['10', '24'])).
% 0.24/0.53  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('28', plain, ((v3_tdlat_3 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('29', plain,
% 0.24/0.53      (((v2_struct_0 @ sk_A)
% 0.24/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.24/0.53  thf('30', plain,
% 0.24/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.24/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.24/0.53  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('32', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.24/0.53      inference('clc', [status(thm)], ['30', '31'])).
% 0.24/0.53  thf(fc2_struct_0, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.24/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.53  thf('33', plain,
% 0.24/0.53      (![X2 : $i]:
% 0.24/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.24/0.53          | ~ (l1_struct_0 @ X2)
% 0.24/0.53          | (v2_struct_0 @ X2))),
% 0.24/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.24/0.53  thf('34', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.24/0.53  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(dt_l1_pre_topc, axiom,
% 0.24/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.53  thf('36', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.24/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.53  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.24/0.53  thf('38', plain, ((v2_struct_0 @ sk_A)),
% 0.24/0.53      inference('demod', [status(thm)], ['34', '37'])).
% 0.24/0.53  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
