%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5a5ZbGSbGq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:28 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 107 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  465 ( 807 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( sk_C @ X29 @ X30 ) @ X29 )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

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

thf('12',plain,(
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('30',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X29: $i,X30: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X32 @ X30 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ X32 )
       != ( sk_C @ X29 @ X30 ) )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X11 @ X10 @ X10 )
        = X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('46',plain,(
    k1_xboole_0
 != ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5a5ZbGSbGq
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 21:08:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.96/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.96/1.20  % Solved by: fo/fo7.sh
% 0.96/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.20  % done 1839 iterations in 0.733s
% 0.96/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.96/1.20  % SZS output start Refutation
% 0.96/1.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.96/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.96/1.20  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.96/1.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.96/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.96/1.20  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.96/1.20  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.96/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.96/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.96/1.20  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.96/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.96/1.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.96/1.20  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.96/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.96/1.20  thf(l13_xboole_0, axiom,
% 0.96/1.20    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.96/1.20  thf('0', plain,
% 0.96/1.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.96/1.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.96/1.20  thf(t4_subset_1, axiom,
% 0.96/1.20    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.96/1.20  thf('1', plain,
% 0.96/1.20      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.96/1.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.96/1.20  thf('2', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.96/1.20      inference('sup+', [status(thm)], ['0', '1'])).
% 0.96/1.20  thf(d5_tex_2, axiom,
% 0.96/1.20    (![A:$i]:
% 0.96/1.20     ( ( l1_pre_topc @ A ) =>
% 0.96/1.20       ( ![B:$i]:
% 0.96/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.20           ( ( v2_tex_2 @ B @ A ) <=>
% 0.96/1.20             ( ![C:$i]:
% 0.96/1.20               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.20                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.96/1.20                      ( ![D:$i]:
% 0.96/1.20                        ( ( m1_subset_1 @
% 0.96/1.20                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.20                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.96/1.20                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.96/1.20                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.96/1.20  thf('3', plain,
% 0.96/1.20      (![X29 : $i, X30 : $i]:
% 0.96/1.20         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.96/1.20          | (r1_tarski @ (sk_C @ X29 @ X30) @ X29)
% 0.96/1.20          | (v2_tex_2 @ X29 @ X30)
% 0.96/1.20          | ~ (l1_pre_topc @ X30))),
% 0.96/1.20      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.96/1.20  thf('4', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         (~ (v1_xboole_0 @ X1)
% 0.96/1.20          | ~ (l1_pre_topc @ X0)
% 0.96/1.20          | (v2_tex_2 @ X1 @ X0)
% 0.96/1.20          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 0.96/1.20      inference('sup-', [status(thm)], ['2', '3'])).
% 0.96/1.20  thf('5', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.96/1.20      inference('sup+', [status(thm)], ['0', '1'])).
% 0.96/1.20  thf(t3_subset, axiom,
% 0.96/1.20    (![A:$i,B:$i]:
% 0.96/1.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.96/1.20  thf('6', plain,
% 0.96/1.20      (![X14 : $i, X15 : $i]:
% 0.96/1.20         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.96/1.20      inference('cnf', [status(esa)], [t3_subset])).
% 0.96/1.20  thf('7', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X1) | (r1_tarski @ X1 @ X0))),
% 0.96/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 0.96/1.20  thf(d10_xboole_0, axiom,
% 0.96/1.20    (![A:$i,B:$i]:
% 0.96/1.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.96/1.20  thf('8', plain,
% 0.96/1.20      (![X1 : $i, X3 : $i]:
% 0.96/1.20         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.96/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.96/1.20  thf('9', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.96/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 0.96/1.20  thf('10', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         ((v2_tex_2 @ X0 @ X1)
% 0.96/1.20          | ~ (l1_pre_topc @ X1)
% 0.96/1.20          | ~ (v1_xboole_0 @ X0)
% 0.96/1.20          | ((sk_C @ X0 @ X1) = (X0))
% 0.96/1.20          | ~ (v1_xboole_0 @ X0))),
% 0.96/1.20      inference('sup-', [status(thm)], ['4', '9'])).
% 0.96/1.20  thf('11', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         (((sk_C @ X0 @ X1) = (X0))
% 0.96/1.20          | ~ (v1_xboole_0 @ X0)
% 0.96/1.20          | ~ (l1_pre_topc @ X1)
% 0.96/1.20          | (v2_tex_2 @ X0 @ X1))),
% 0.96/1.20      inference('simplify', [status(thm)], ['10'])).
% 0.96/1.20  thf(t35_tex_2, conjecture,
% 0.96/1.20    (![A:$i]:
% 0.96/1.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.96/1.20       ( ![B:$i]:
% 0.96/1.20         ( ( ( v1_xboole_0 @ B ) & 
% 0.96/1.20             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.96/1.20           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.96/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.20    (~( ![A:$i]:
% 0.96/1.20        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.96/1.20            ( l1_pre_topc @ A ) ) =>
% 0.96/1.20          ( ![B:$i]:
% 0.96/1.20            ( ( ( v1_xboole_0 @ B ) & 
% 0.96/1.20                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.96/1.20              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.96/1.20    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.96/1.20  thf('12', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.96/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.20  thf('13', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.96/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.20  thf('14', plain,
% 0.96/1.20      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.96/1.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.96/1.20  thf('15', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.96/1.20      inference('sup-', [status(thm)], ['13', '14'])).
% 0.96/1.20  thf('16', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.96/1.20      inference('demod', [status(thm)], ['12', '15'])).
% 0.96/1.20  thf('17', plain,
% 0.96/1.20      ((~ (l1_pre_topc @ sk_A)
% 0.96/1.20        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.96/1.20        | ((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.96/1.20      inference('sup-', [status(thm)], ['11', '16'])).
% 0.96/1.20  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.96/1.20  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.96/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.96/1.20  thf('20', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.96/1.20      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.96/1.20  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.20  thf('22', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.96/1.20      inference('sup+', [status(thm)], ['0', '1'])).
% 0.96/1.20  thf(cc1_tops_1, axiom,
% 0.96/1.20    (![A:$i]:
% 0.96/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.96/1.20       ( ![B:$i]:
% 0.96/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.96/1.20           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.96/1.20  thf('23', plain,
% 0.96/1.20      (![X27 : $i, X28 : $i]:
% 0.96/1.20         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.96/1.20          | (v3_pre_topc @ X27 @ X28)
% 0.96/1.20          | ~ (v1_xboole_0 @ X27)
% 0.96/1.20          | ~ (l1_pre_topc @ X28)
% 0.96/1.20          | ~ (v2_pre_topc @ X28))),
% 0.96/1.20      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.96/1.20  thf('24', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         (~ (v1_xboole_0 @ X1)
% 0.96/1.20          | ~ (v2_pre_topc @ X0)
% 0.96/1.20          | ~ (l1_pre_topc @ X0)
% 0.96/1.20          | ~ (v1_xboole_0 @ X1)
% 0.96/1.20          | (v3_pre_topc @ X1 @ X0))),
% 0.96/1.20      inference('sup-', [status(thm)], ['22', '23'])).
% 0.96/1.20  thf('25', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         ((v3_pre_topc @ X1 @ X0)
% 0.96/1.20          | ~ (l1_pre_topc @ X0)
% 0.96/1.20          | ~ (v2_pre_topc @ X0)
% 0.96/1.20          | ~ (v1_xboole_0 @ X1))),
% 0.96/1.20      inference('simplify', [status(thm)], ['24'])).
% 0.96/1.20  thf('26', plain,
% 0.96/1.20      (![X0 : $i]:
% 0.96/1.20         (~ (v1_xboole_0 @ X0)
% 0.96/1.20          | ~ (v2_pre_topc @ sk_A)
% 0.96/1.20          | (v3_pre_topc @ X0 @ sk_A))),
% 0.96/1.20      inference('sup-', [status(thm)], ['21', '25'])).
% 0.96/1.20  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.96/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.20  thf('28', plain,
% 0.96/1.20      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.96/1.20      inference('demod', [status(thm)], ['26', '27'])).
% 0.96/1.20  thf('29', plain,
% 0.96/1.20      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.96/1.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.96/1.20  thf('30', plain,
% 0.96/1.20      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.96/1.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.96/1.20  thf('31', plain,
% 0.96/1.20      (![X29 : $i, X30 : $i, X32 : $i]:
% 0.96/1.20         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.96/1.20          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.96/1.20          | ~ (v3_pre_topc @ X32 @ X30)
% 0.96/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X30) @ X29 @ X32)
% 0.96/1.20              != (sk_C @ X29 @ X30))
% 0.96/1.20          | (v2_tex_2 @ X29 @ X30)
% 0.96/1.20          | ~ (l1_pre_topc @ X30))),
% 0.96/1.20      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.96/1.20  thf('32', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]:
% 0.96/1.20         (~ (l1_pre_topc @ X0)
% 0.96/1.20          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.96/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.96/1.20              != (sk_C @ k1_xboole_0 @ X0))
% 0.96/1.20          | ~ (v3_pre_topc @ X1 @ X0)
% 0.96/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.96/1.20      inference('sup-', [status(thm)], ['30', '31'])).
% 0.96/1.20  thf('33', plain,
% 0.96/1.20      (![X0 : $i]:
% 0.96/1.20         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.96/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.96/1.20              != (sk_C @ k1_xboole_0 @ X0))
% 0.96/1.20          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.96/1.20          | ~ (l1_pre_topc @ X0))),
% 0.96/1.20      inference('sup-', [status(thm)], ['29', '32'])).
% 0.96/1.20  thf('34', plain,
% 0.96/1.20      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.96/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.96/1.20  thf('35', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.96/1.20      inference('simplify', [status(thm)], ['34'])).
% 0.96/1.20  thf('36', plain,
% 0.96/1.20      (![X14 : $i, X16 : $i]:
% 0.96/1.20         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.96/1.20      inference('cnf', [status(esa)], [t3_subset])).
% 0.96/1.20  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.96/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 0.96/1.20  thf(idempotence_k9_subset_1, axiom,
% 0.96/1.20    (![A:$i,B:$i,C:$i]:
% 0.96/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.96/1.20       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.96/1.20  thf('38', plain,
% 0.96/1.20      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.96/1.20         (((k9_subset_1 @ X11 @ X10 @ X10) = (X10))
% 0.96/1.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.96/1.20      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.96/1.20  thf('39', plain,
% 0.96/1.20      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.96/1.20      inference('sup-', [status(thm)], ['37', '38'])).
% 0.96/1.20  thf('40', plain,
% 0.96/1.20      (![X0 : $i]:
% 0.96/1.20         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.96/1.20          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.96/1.20          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.96/1.20          | ~ (l1_pre_topc @ X0))),
% 0.96/1.20      inference('demod', [status(thm)], ['33', '39'])).
% 0.96/1.20  thf('41', plain,
% 0.96/1.20      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.96/1.20        | ~ (l1_pre_topc @ sk_A)
% 0.96/1.20        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.96/1.20        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.96/1.20      inference('sup-', [status(thm)], ['28', '40'])).
% 0.96/1.20  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.96/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.96/1.20  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.96/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.20  thf('44', plain,
% 0.96/1.20      (((v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.96/1.20        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.96/1.20      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.96/1.20  thf('45', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.96/1.20      inference('demod', [status(thm)], ['12', '15'])).
% 0.96/1.20  thf('46', plain, (((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A))),
% 0.96/1.20      inference('clc', [status(thm)], ['44', '45'])).
% 0.96/1.20  thf('47', plain, ($false),
% 0.96/1.20      inference('simplify_reflect-', [status(thm)], ['20', '46'])).
% 0.96/1.20  
% 0.96/1.20  % SZS output end Refutation
% 0.96/1.20  
% 0.96/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
