%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7sUvDdOK8t

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:26 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   67 (  87 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  436 ( 820 expanded)
%              Number of equality atoms :   39 (  48 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(t59_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X3 @ X2 )
        = ( k6_setfam_1 @ X3 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('4',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k6_setfam_1 @ X7 @ X6 )
        = ( k1_setfam_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('7',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X3 @ X2 )
        = ( k6_setfam_1 @ X3 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('11',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k6_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k6_setfam_1 @ X7 @ X6 )
        = ( k1_setfam_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('16',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ ( k1_setfam_1 @ X18 ) @ ( k1_setfam_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','21'])).

thf('23',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','30'])).

thf('32',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X3 @ X2 )
        = X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('34',plain,(
    ! [X3: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) )
      | ( ( k8_setfam_1 @ X3 @ k1_xboole_0 )
        = X3 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k8_setfam_1 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('39',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32','36','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7sUvDdOK8t
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 175 iterations in 0.101s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.55  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.38/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.55  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.38/0.55  thf(t59_setfam_1, conjecture,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( ![C:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55           ( ( r1_tarski @ B @ C ) =>
% 0.38/0.55             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i,B:$i]:
% 0.38/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55          ( ![C:$i]:
% 0.38/0.55            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55              ( ( r1_tarski @ B @ C ) =>
% 0.38/0.55                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.38/0.55          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t7_xboole_0, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d10_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.55           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.38/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i]:
% 0.38/0.55         (((X2) = (k1_xboole_0))
% 0.38/0.55          | ((k8_setfam_1 @ X3 @ X2) = (k6_setfam_1 @ X3 @ X2))
% 0.38/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.38/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.38/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(redefinition_k6_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i]:
% 0.38/0.55         (((k6_setfam_1 @ X7 @ X6) = (k1_setfam_1 @ X6))
% 0.38/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.55  thf('7', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))
% 0.38/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i]:
% 0.38/0.55         (((X2) = (k1_xboole_0))
% 0.38/0.55          | ((k8_setfam_1 @ X3 @ X2) = (k6_setfam_1 @ X3 @ X2))
% 0.38/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.38/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.38/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.38/0.55          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      ((~ (r1_tarski @ (k6_setfam_1 @ sk_A @ sk_C) @ 
% 0.38/0.55           (k8_setfam_1 @ sk_A @ sk_B_1))
% 0.38/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i]:
% 0.38/0.55         (((k6_setfam_1 @ X7 @ X6) = (k1_setfam_1 @ X6))
% 0.38/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.55  thf('16', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B_1))
% 0.38/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['13', '16'])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.38/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.38/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['8', '17'])).
% 0.38/0.55  thf('19', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t7_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.55         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         (((X17) = (k1_xboole_0))
% 0.38/0.55          | ~ (r1_tarski @ X17 @ X18)
% 0.38/0.55          | (r1_tarski @ (k1_setfam_1 @ X18) @ (k1_setfam_1 @ X17)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.38/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.55  thf('22', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.55      inference('clc', [status(thm)], ['18', '21'])).
% 0.38/0.55  thf('23', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t3_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X8 : $i, X10 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('25', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.55  thf(t5_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X14 @ X15)
% 0.38/0.55          | ~ (v1_xboole_0 @ X16)
% 0.38/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.38/0.55          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['22', '27'])).
% 0.38/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.55  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X0 : $i]: (((sk_B_1) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.38/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.55  thf('31', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '30'])).
% 0.38/0.55  thf('32', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i]:
% 0.38/0.55         (((X2) != (k1_xboole_0))
% 0.38/0.55          | ((k8_setfam_1 @ X3 @ X2) = (X3))
% 0.38/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.38/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X3 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3)))
% 0.38/0.55          | ((k8_setfam_1 @ X3 @ k1_xboole_0) = (X3)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.55  thf(t4_subset_1, axiom,
% 0.38/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.55  thf('36', plain, (![X3 : $i]: ((k8_setfam_1 @ X3 @ k1_xboole_0) = (X3))),
% 0.38/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(dt_k8_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X4 : $i, X5 : $i]:
% 0.38/0.55         ((m1_subset_1 @ (k8_setfam_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]:
% 0.38/0.55         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('41', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.55  thf('42', plain, ($false),
% 0.38/0.55      inference('demod', [status(thm)], ['0', '32', '36', '41'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
