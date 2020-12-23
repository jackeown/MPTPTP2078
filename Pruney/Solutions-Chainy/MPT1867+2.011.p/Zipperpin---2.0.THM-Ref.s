%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bzglfXf4TK

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:27 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 100 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  429 ( 780 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( sk_C @ X23 @ X24 ) @ X23 )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('15',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_pre_topc @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X26 )
       != ( sk_C @ X23 @ X24 ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X12 @ X11 @ X11 )
        = X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['4','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bzglfXf4TK
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 103 iterations in 0.064s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.35/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(t35_tex_2, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( ( v1_xboole_0 @ B ) & 
% 0.35/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.54            ( l1_pre_topc @ A ) ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( ( v1_xboole_0 @ B ) & 
% 0.35/0.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.35/0.54  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(l13_xboole_0, axiom,
% 0.35/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.54  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.54  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.38/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.54  thf(t4_subset_1, axiom,
% 0.38/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.54  thf('5', plain,
% 0.38/0.54      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.54  thf(d5_tex_2, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( l1_pre_topc @ A ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54           ( ( v2_tex_2 @ B @ A ) <=>
% 0.38/0.54             ( ![C:$i]:
% 0.38/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.38/0.54                      ( ![D:$i]:
% 0.38/0.54                        ( ( m1_subset_1 @
% 0.38/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.38/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.38/0.54                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.54  thf('6', plain,
% 0.38/0.54      (![X23 : $i, X24 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.38/0.54          | (r1_tarski @ (sk_C @ X23 @ X24) @ X23)
% 0.38/0.54          | (v2_tex_2 @ X23 @ X24)
% 0.38/0.54          | ~ (l1_pre_topc @ X24))),
% 0.38/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.38/0.54  thf('7', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X0)
% 0.38/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.54          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.54  thf('8', plain,
% 0.38/0.54      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.54  thf(t3_subset, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.54  thf('9', plain,
% 0.38/0.54      (![X15 : $i, X16 : $i]:
% 0.38/0.54         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.38/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.54  thf('10', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.54  thf(d10_xboole_0, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.54  thf('11', plain,
% 0.38/0.54      (![X4 : $i, X6 : $i]:
% 0.38/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.54  thf('12', plain,
% 0.38/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.54  thf('13', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.54          | ~ (l1_pre_topc @ X0)
% 0.38/0.54          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['7', '12'])).
% 0.38/0.54  thf('14', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.38/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.54  thf('15', plain,
% 0.38/0.54      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.54  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('17', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.38/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.54  thf('18', plain,
% 0.38/0.54      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.54  thf(cc1_tops_1, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.38/0.54  thf('19', plain,
% 0.38/0.54      (![X21 : $i, X22 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.54          | (v3_pre_topc @ X21 @ X22)
% 0.38/0.54          | ~ (v1_xboole_0 @ X21)
% 0.38/0.54          | ~ (l1_pre_topc @ X22)
% 0.38/0.54          | ~ (v2_pre_topc @ X22))),
% 0.38/0.54      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.38/0.54  thf('20', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (v2_pre_topc @ X0)
% 0.38/0.54          | ~ (l1_pre_topc @ X0)
% 0.38/0.54          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.54          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.54  thf('21', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('22', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.54  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.54  thf('24', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (v2_pre_topc @ X0)
% 0.38/0.54          | ~ (l1_pre_topc @ X0)
% 0.38/0.54          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.54      inference('demod', [status(thm)], ['20', '23'])).
% 0.38/0.54  thf('25', plain,
% 0.38/0.54      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.54  thf('26', plain,
% 0.38/0.54      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.54  thf('27', plain,
% 0.38/0.54      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.38/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.38/0.54          | ~ (v3_pre_topc @ X26 @ X24)
% 0.38/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X26)
% 0.38/0.54              != (sk_C @ X23 @ X24))
% 0.38/0.54          | (v2_tex_2 @ X23 @ X24)
% 0.38/0.54          | ~ (l1_pre_topc @ X24))),
% 0.38/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.38/0.54  thf('28', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X0)
% 0.38/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.38/0.54              != (sk_C @ k1_xboole_0 @ X0))
% 0.38/0.54          | ~ (v3_pre_topc @ X1 @ X0)
% 0.38/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.54  thf('29', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.38/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.38/0.54              != (sk_C @ k1_xboole_0 @ X0))
% 0.38/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.54          | ~ (l1_pre_topc @ X0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['25', '28'])).
% 0.38/0.54  thf('30', plain,
% 0.38/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.38/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.54  thf('31', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.38/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.54  thf('32', plain,
% 0.38/0.54      (![X15 : $i, X17 : $i]:
% 0.38/0.54         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.38/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.54  thf('33', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.54  thf(idempotence_k9_subset_1, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i]:
% 0.38/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.54       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.38/0.54  thf('34', plain,
% 0.38/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.54         (((k9_subset_1 @ X12 @ X11 @ X11) = (X11))
% 0.38/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.54      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.38/0.54  thf('35', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.38/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.54  thf('36', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.38/0.54          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.38/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.54          | ~ (l1_pre_topc @ X0))),
% 0.38/0.54      inference('demod', [status(thm)], ['29', '35'])).
% 0.38/0.54  thf('37', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X0)
% 0.38/0.54          | ~ (v2_pre_topc @ X0)
% 0.38/0.54          | ~ (l1_pre_topc @ X0)
% 0.38/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.54          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['24', '36'])).
% 0.38/0.54  thf('38', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.38/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.54          | ~ (v2_pre_topc @ X0)
% 0.38/0.54          | ~ (l1_pre_topc @ X0))),
% 0.38/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.54  thf('39', plain,
% 0.38/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.54        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['17', '38'])).
% 0.38/0.54  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('42', plain,
% 0.38/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.38/0.54      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.38/0.54  thf('43', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.38/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.54  thf('44', plain, ($false), inference('demod', [status(thm)], ['4', '43'])).
% 0.38/0.54  
% 0.38/0.54  % SZS output end Refutation
% 0.38/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
