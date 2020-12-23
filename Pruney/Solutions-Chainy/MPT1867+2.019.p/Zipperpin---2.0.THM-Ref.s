%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SQlxB4la6R

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:28 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 139 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  520 (1121 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('8',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( sk_C @ X15 @ X16 ) @ X15 )
      | ( v2_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ sk_B_2 @ X0 )
      | ( r1_tarski @ ( sk_C @ sk_B_2 @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_2 @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_2 )
      | ( X0 = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ sk_B_2 @ X0 )
        = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('25',plain,(
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_C @ sk_B_2 @ sk_A )
      = sk_B_2 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','30'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X7 @ X6 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ X18 )
       != ( sk_C @ X15 @ X16 ) )
      | ( v2_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ X2 )
       != ( sk_C @ X1 @ X0 ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ X1 )
       != ( sk_C @ X2 @ X0 ) )
      | ( v2_tex_2 @ X2 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ X0 @ X1 )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
       != ( sk_C @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','49'])).

thf('51',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['50','51','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SQlxB4la6R
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:14:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.99/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.20  % Solved by: fo/fo7.sh
% 0.99/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.20  % done 1501 iterations in 0.740s
% 0.99/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.20  % SZS output start Refutation
% 0.99/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.99/1.20  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.99/1.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.20  thf(sk_B_type, type, sk_B: $i > $i).
% 0.99/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.20  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.99/1.20  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.99/1.20  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.99/1.20  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.99/1.20  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.99/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.99/1.20  thf(rc2_subset_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ?[B:$i]:
% 0.99/1.20       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.99/1.20  thf('0', plain, (![X9 : $i]: (v1_xboole_0 @ (sk_B_1 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.99/1.20  thf(t8_boole, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.99/1.20  thf('1', plain,
% 0.99/1.20      (![X3 : $i, X4 : $i]:
% 0.99/1.20         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t8_boole])).
% 0.99/1.20  thf('2', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]: (((sk_B_1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.20  thf('3', plain,
% 0.99/1.20      (![X9 : $i]: (m1_subset_1 @ (sk_B_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.99/1.20  thf('4', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.99/1.20  thf(cc1_tops_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.99/1.20  thf('5', plain,
% 0.99/1.20      (![X13 : $i, X14 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.99/1.20          | (v3_pre_topc @ X13 @ X14)
% 0.99/1.20          | ~ (v1_xboole_0 @ X13)
% 0.99/1.20          | ~ (l1_pre_topc @ X14)
% 0.99/1.20          | ~ (v2_pre_topc @ X14))),
% 0.99/1.20      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.99/1.20  thf('6', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (~ (v1_xboole_0 @ X1)
% 0.99/1.20          | ~ (v2_pre_topc @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | ~ (v1_xboole_0 @ X1)
% 0.99/1.20          | (v3_pre_topc @ X1 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.20  thf('7', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((v3_pre_topc @ X1 @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | ~ (v2_pre_topc @ X0)
% 0.99/1.20          | ~ (v1_xboole_0 @ X1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['6'])).
% 0.99/1.20  thf(t35_tex_2, conjecture,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( ( v1_xboole_0 @ B ) & 
% 0.99/1.20             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.20           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.99/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.20    (~( ![A:$i]:
% 0.99/1.20        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.99/1.20            ( l1_pre_topc @ A ) ) =>
% 0.99/1.20          ( ![B:$i]:
% 0.99/1.20            ( ( ( v1_xboole_0 @ B ) & 
% 0.99/1.20                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.20              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.99/1.20    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.99/1.20  thf('8', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('9', plain,
% 0.99/1.20      (![X3 : $i, X4 : $i]:
% 0.99/1.20         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t8_boole])).
% 0.99/1.20  thf('10', plain, (![X0 : $i]: (((sk_B_2) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['8', '9'])).
% 0.99/1.20  thf('11', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('12', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]: (((sk_B_1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.20  thf('13', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (sk_B_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['11', '12'])).
% 0.99/1.20  thf('14', plain,
% 0.99/1.20      (![X9 : $i]: (m1_subset_1 @ (sk_B_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.99/1.20  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ X0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['13', '14'])).
% 0.99/1.20  thf(d5_tex_2, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_pre_topc @ A ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20           ( ( v2_tex_2 @ B @ A ) <=>
% 0.99/1.20             ( ![C:$i]:
% 0.99/1.20               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.99/1.20                      ( ![D:$i]:
% 0.99/1.20                        ( ( m1_subset_1 @
% 0.99/1.20                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.99/1.20                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.99/1.20                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.99/1.20  thf('16', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.99/1.20          | (r1_tarski @ (sk_C @ X15 @ X16) @ X15)
% 0.99/1.20          | (v2_tex_2 @ X15 @ X16)
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.99/1.20  thf('17', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X0)
% 0.99/1.20          | (v2_tex_2 @ sk_B_2 @ X0)
% 0.99/1.20          | (r1_tarski @ (sk_C @ sk_B_2 @ X0) @ sk_B_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 0.99/1.20  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ X0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['13', '14'])).
% 0.99/1.20  thf(t3_subset, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.20  thf('19', plain,
% 0.99/1.20      (![X10 : $i, X11 : $i]:
% 0.99/1.20         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.20  thf('20', plain, (![X0 : $i]: (r1_tarski @ sk_B_2 @ X0)),
% 0.99/1.20      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.20  thf(d10_xboole_0, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.20  thf('21', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('22', plain,
% 0.99/1.20      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B_2) | ((X0) = (sk_B_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['20', '21'])).
% 0.99/1.20  thf('23', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_tex_2 @ sk_B_2 @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | ((sk_C @ sk_B_2 @ X0) = (sk_B_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['17', '22'])).
% 0.99/1.20  thf('24', plain, (![X0 : $i]: (((sk_B_2) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['8', '9'])).
% 0.99/1.20  thf('25', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('26', plain,
% 0.99/1.20      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['24', '25'])).
% 0.99/1.20  thf('27', plain,
% 0.99/1.20      ((((sk_C @ sk_B_2 @ sk_A) = (sk_B_2))
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | ~ (v1_xboole_0 @ sk_B_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['23', '26'])).
% 0.99/1.20  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('29', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('30', plain, (((sk_C @ sk_B_2 @ sk_A) = (sk_B_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.99/1.20  thf('31', plain,
% 0.99/1.20      (![X0 : $i]: (((sk_C @ X0 @ sk_A) = (sk_B_2)) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['10', '30'])).
% 0.99/1.20  thf(existence_m1_subset_1, axiom,
% 0.99/1.20    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.99/1.20  thf('32', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.99/1.20      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.99/1.20  thf(idempotence_k9_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.20       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.99/1.20  thf('33', plain,
% 0.99/1.20      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.99/1.20         (((k9_subset_1 @ X7 @ X6 @ X6) = (X6))
% 0.99/1.20          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.99/1.20      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.99/1.20  thf('34', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['32', '33'])).
% 0.99/1.20  thf('35', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.99/1.20  thf('36', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.99/1.20  thf('37', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.99/1.20          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.99/1.20          | ~ (v3_pre_topc @ X18 @ X16)
% 0.99/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ X18)
% 0.99/1.20              != (sk_C @ X15 @ X16))
% 0.99/1.20          | (v2_tex_2 @ X15 @ X16)
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.99/1.20  thf('38', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.20         (~ (v1_xboole_0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | (v2_tex_2 @ X1 @ X0)
% 0.99/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ X2) != (sk_C @ X1 @ X0))
% 0.99/1.20          | ~ (v3_pre_topc @ X2 @ X0)
% 0.99/1.20          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['36', '37'])).
% 0.99/1.20  thf('39', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.20         (~ (v1_xboole_0 @ X1)
% 0.99/1.20          | ~ (v3_pre_topc @ X1 @ X0)
% 0.99/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ X1) != (sk_C @ X2 @ X0))
% 0.99/1.20          | (v2_tex_2 @ X2 @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | ~ (v1_xboole_0 @ X2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['35', '38'])).
% 0.99/1.20  thf('40', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (((X0) != (sk_C @ X0 @ X1))
% 0.99/1.20          | ~ (v1_xboole_0 @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | (v2_tex_2 @ X0 @ X1)
% 0.99/1.20          | ~ (v3_pre_topc @ X0 @ X1)
% 0.99/1.20          | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['34', '39'])).
% 0.99/1.20  thf('41', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (~ (v3_pre_topc @ X0 @ X1)
% 0.99/1.20          | (v2_tex_2 @ X0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (v1_xboole_0 @ X0)
% 0.99/1.20          | ((X0) != (sk_C @ X0 @ X1)))),
% 0.99/1.20      inference('simplify', [status(thm)], ['40'])).
% 0.99/1.20  thf('42', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (((X0) != (sk_B_2))
% 0.99/1.20          | ~ (v1_xboole_0 @ X0)
% 0.99/1.20          | ~ (v1_xboole_0 @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_A)
% 0.99/1.20          | (v2_tex_2 @ X0 @ sk_A)
% 0.99/1.20          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['31', '41'])).
% 0.99/1.20  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('44', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (((X0) != (sk_B_2))
% 0.99/1.20          | ~ (v1_xboole_0 @ X0)
% 0.99/1.20          | ~ (v1_xboole_0 @ X0)
% 0.99/1.20          | (v2_tex_2 @ X0 @ sk_A)
% 0.99/1.20          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.99/1.20      inference('demod', [status(thm)], ['42', '43'])).
% 0.99/1.20  thf('45', plain,
% 0.99/1.20      ((~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.99/1.20        | (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.99/1.20        | ~ (v1_xboole_0 @ sk_B_2))),
% 0.99/1.20      inference('simplify', [status(thm)], ['44'])).
% 0.99/1.20  thf('46', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('47', plain,
% 0.99/1.20      ((~ (v3_pre_topc @ sk_B_2 @ sk_A) | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.99/1.20      inference('simplify_reflect+', [status(thm)], ['45', '46'])).
% 0.99/1.20  thf('48', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('49', plain, (~ (v3_pre_topc @ sk_B_2 @ sk_A)),
% 0.99/1.20      inference('clc', [status(thm)], ['47', '48'])).
% 0.99/1.20  thf('50', plain,
% 0.99/1.20      ((~ (v1_xboole_0 @ sk_B_2)
% 0.99/1.20        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['7', '49'])).
% 0.99/1.20  thf('51', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('54', plain, ($false),
% 0.99/1.20      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.99/1.20  
% 0.99/1.20  % SZS output end Refutation
% 0.99/1.20  
% 0.99/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
