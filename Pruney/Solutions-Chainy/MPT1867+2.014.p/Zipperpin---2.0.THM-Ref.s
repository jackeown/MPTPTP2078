%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.knPj81Wmhq

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 (  93 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  432 ( 700 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ ( sk_C @ X24 @ X25 ) @ X24 )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('18',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X27 @ X25 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ X27 )
       != ( sk_C @ X24 @ X25 ) )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X14 @ X13 @ X13 )
        = X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['4','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.knPj81Wmhq
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 231 iterations in 0.080s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(t35_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.21/0.54  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l13_xboole_0, axiom,
% 0.21/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.54  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.54  thf(t4_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf(d5_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.21/0.54                      ( ![D:$i]:
% 0.21/0.54                        ( ( m1_subset_1 @
% 0.21/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.54                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.54          | (r1_tarski @ (sk_C @ X24 @ X25) @ X24)
% 0.21/0.54          | (v2_tex_2 @ X24 @ X25)
% 0.21/0.54          | ~ (l1_pre_topc @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('9', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.54  thf(l32_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X7 : $i, X9 : $i]:
% 0.21/0.54         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.54  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf(t36_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.21/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.54  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X4 : $i, X6 : $i]:
% 0.21/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '15'])).
% 0.21/0.54  thf('17', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('20', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf(cc1_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.54          | (v3_pre_topc @ X22 @ X23)
% 0.21/0.54          | ~ (v1_xboole_0 @ X22)
% 0.21/0.54          | ~ (l1_pre_topc @ X23)
% 0.21/0.54          | ~ (v2_pre_topc @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.54          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.54  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i, X27 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.54          | ~ (v3_pre_topc @ X27 @ X25)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X25) @ X24 @ X27)
% 0.21/0.54              != (sk_C @ X24 @ X25))
% 0.21/0.54          | (v2_tex_2 @ X24 @ X25)
% 0.21/0.54          | ~ (l1_pre_topc @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.21/0.54              != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.54          | ~ (v3_pre_topc @ X1 @ X0)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.54              != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf(idempotence_k9_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.54         (((k9_subset_1 @ X14 @ X13 @ X13) = (X13))
% 0.21/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.54          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['30', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '36'])).
% 0.21/0.54  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.54  thf('41', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf('42', plain, ($false), inference('demod', [status(thm)], ['4', '41'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
