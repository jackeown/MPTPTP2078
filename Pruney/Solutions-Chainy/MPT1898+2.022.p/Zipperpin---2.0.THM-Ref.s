%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0AWKl1YCMf

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:41 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 174 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  508 (1446 expanded)
%              Number of equality atoms :   14 (  42 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k6_subset_1 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k6_subset_1 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( m1_subset_1 @ ( sk_C @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X22: $i] :
      ( ~ ( v3_tex_2 @ X22 @ sk_A )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( v3_tex_2 @ ( sk_C @ X20 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['40','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0AWKl1YCMf
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 425 iterations in 0.156s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.40/0.60  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.40/0.60  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.40/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(t66_tex_2, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.40/0.60         ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ?[B:$i]:
% 0.40/0.60         ( ( v3_tex_2 @ B @ A ) & 
% 0.40/0.60           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.60            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60          ( ?[B:$i]:
% 0.40/0.60            ( ( v3_tex_2 @ B @ A ) & 
% 0.40/0.60              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.40/0.60  thf('0', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t34_mcart_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60          ( ![B:$i]:
% 0.40/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.40/0.60                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.60                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.40/0.60                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X13 : $i]:
% 0.40/0.60         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.40/0.60      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.40/0.60  thf(dt_k6_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X3 : $i, X4 : $i]:
% 0.40/0.60         (m1_subset_1 @ (k6_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.40/0.60  thf(t5_subset, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.40/0.60          ( v1_xboole_0 @ C ) ) ))).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X10 @ X11)
% 0.40/0.60          | ~ (v1_xboole_0 @ X12)
% 0.40/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t5_subset])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k6_subset_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.40/0.60  thf(l32_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.60  thf(redefinition_k6_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X5 : $i, X6 : $i]: ((k6_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1) | ((k6_subset_1 @ X0 @ X1) != (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.60          | ~ (v1_xboole_0 @ X1)
% 0.40/0.60          | (r1_tarski @ X1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X1 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.60      inference('simplify', [status(thm)], ['9'])).
% 0.40/0.60  thf(t3_subset, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X7 : $i, X9 : $i]:
% 0.40/0.60         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.60  thf(t35_tex_2, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( v1_xboole_0 @ B ) & 
% 0.40/0.60             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.60           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ X18)
% 0.40/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.40/0.60          | (v2_tex_2 @ X18 @ X19)
% 0.40/0.60          | ~ (l1_pre_topc @ X19)
% 0.40/0.60          | ~ (v2_pre_topc @ X19)
% 0.40/0.60          | (v2_struct_0 @ X19))),
% 0.40/0.60      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ X1)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (v2_pre_topc @ X0)
% 0.40/0.60          | ~ (l1_pre_topc @ X0)
% 0.40/0.60          | (v2_tex_2 @ X1 @ X0)
% 0.40/0.60          | ~ (v1_xboole_0 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((v2_tex_2 @ X1 @ X0)
% 0.40/0.60          | ~ (l1_pre_topc @ X0)
% 0.40/0.60          | ~ (v2_pre_topc @ X0)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (v1_xboole_0 @ X1))),
% 0.40/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ X0)
% 0.40/0.60          | (v2_struct_0 @ sk_A)
% 0.40/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.60          | (v2_tex_2 @ X0 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '15'])).
% 0.40/0.60  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ X0) | (v2_struct_0 @ sk_A) | (v2_tex_2 @ X0 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.60  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X0 : $i]: ((v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['18', '19'])).
% 0.40/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.60  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k6_subset_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1) | ((k6_subset_1 @ X0 @ X1) != (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.60  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X7 : $i, X9 : $i]:
% 0.40/0.60         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.60  thf(t65_tex_2, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.40/0.60         ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.40/0.60                ( ![C:$i]:
% 0.40/0.60                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X20 : $i, X21 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.40/0.60          | ~ (v2_tex_2 @ X20 @ X21)
% 0.40/0.60          | (m1_subset_1 @ (sk_C @ X20 @ X21) @ 
% 0.40/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.40/0.60          | ~ (l1_pre_topc @ X21)
% 0.40/0.60          | ~ (v3_tdlat_3 @ X21)
% 0.40/0.60          | ~ (v2_pre_topc @ X21)
% 0.40/0.60          | (v2_struct_0 @ X21))),
% 0.40/0.60      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ X0)
% 0.40/0.60          | ~ (v2_pre_topc @ X0)
% 0.40/0.60          | ~ (v3_tdlat_3 @ X0)
% 0.40/0.60          | ~ (l1_pre_topc @ X0)
% 0.40/0.60          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.40/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.40/0.60          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.60        | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ~ (v3_tdlat_3 @ sk_A)
% 0.40/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.60        | (v2_struct_0 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['20', '30'])).
% 0.40/0.60  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.60  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('34', plain, ((v3_tdlat_3 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.40/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.60        | (v2_struct_0 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.40/0.60  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      ((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.40/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('clc', [status(thm)], ['36', '37'])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X22 : $i]:
% 0.40/0.60         (~ (v3_tex_2 @ X22 @ sk_A)
% 0.40/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('40', plain, (~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.40/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.60  thf('41', plain,
% 0.40/0.60      (![X0 : $i]: ((v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['18', '19'])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X20 : $i, X21 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.40/0.60          | ~ (v2_tex_2 @ X20 @ X21)
% 0.40/0.60          | (v3_tex_2 @ (sk_C @ X20 @ X21) @ X21)
% 0.40/0.60          | ~ (l1_pre_topc @ X21)
% 0.40/0.60          | ~ (v3_tdlat_3 @ X21)
% 0.40/0.60          | ~ (v2_pre_topc @ X21)
% 0.40/0.60          | (v2_struct_0 @ X21))),
% 0.40/0.60      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ X0)
% 0.40/0.60          | ~ (v2_pre_topc @ X0)
% 0.40/0.60          | ~ (v3_tdlat_3 @ X0)
% 0.40/0.60          | ~ (l1_pre_topc @ X0)
% 0.40/0.60          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.40/0.60          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.60        | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.40/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ~ (v3_tdlat_3 @ sk_A)
% 0.40/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.60        | (v2_struct_0 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['41', '44'])).
% 0.40/0.60  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.60  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('48', plain, ((v3_tdlat_3 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('50', plain,
% 0.40/0.60      (((v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.40/0.60  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('52', plain, ((v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.40/0.60      inference('clc', [status(thm)], ['50', '51'])).
% 0.40/0.60  thf('53', plain, ($false), inference('demod', [status(thm)], ['40', '52'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
