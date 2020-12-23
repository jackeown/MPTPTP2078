%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.usjfGUEY1z

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:25 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   64 (  83 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  441 ( 818 expanded)
%              Number of equality atoms :   42 (  51 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ X32 )
      | ( r1_tarski @ ( k1_setfam_1 @ X32 ) @ ( k1_setfam_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = ( k6_setfam_1 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('6',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k6_setfam_1 @ X22 @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = ( k6_setfam_1 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('13',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k6_setfam_1 @ X22 @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('33',plain,(
    ! [X18: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( ( k8_setfam_1 @ X18 @ k1_xboole_0 )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k8_setfam_1 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('38',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31','35','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.usjfGUEY1z
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 365 iterations in 0.175s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.36/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.60  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.36/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(t59_setfam_1, conjecture,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.60       ( ![C:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.60           ( ( r1_tarski @ B @ C ) =>
% 0.36/0.60             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i,B:$i]:
% 0.36/0.60        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.60          ( ![C:$i]:
% 0.36/0.60            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.60              ( ( r1_tarski @ B @ C ) =>
% 0.36/0.60                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.60          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('1', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t7_setfam_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.60         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X31 : $i, X32 : $i]:
% 0.36/0.60         (((X31) = (k1_xboole_0))
% 0.36/0.60          | ~ (r1_tarski @ X31 @ X32)
% 0.36/0.60          | (r1_tarski @ (k1_setfam_1 @ X32) @ (k1_setfam_1 @ X31)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (((r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.36/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(d10_setfam_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.60       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.60           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.36/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         (((X17) = (k1_xboole_0))
% 0.36/0.60          | ((k8_setfam_1 @ X18 @ X17) = (k6_setfam_1 @ X18 @ X17))
% 0.36/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.36/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k6_setfam_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.60       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (![X21 : $i, X22 : $i]:
% 0.36/0.60         (((k6_setfam_1 @ X22 @ X21) = (k1_setfam_1 @ X21))
% 0.36/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.36/0.60  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.36/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['6', '9'])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         (((X17) = (k1_xboole_0))
% 0.36/0.60          | ((k8_setfam_1 @ X18 @ X17) = (k6_setfam_1 @ X18 @ X17))
% 0.36/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.36/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.60          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.60           (k6_setfam_1 @ sk_A @ sk_B))
% 0.36/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X21 : $i, X22 : $i]:
% 0.36/0.60         (((k6_setfam_1 @ X22 @ X21) = (k1_setfam_1 @ X21))
% 0.36/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.36/0.60  thf('18', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.36/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['15', '18'])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.36/0.60        | ((sk_C_1) = (k1_xboole_0))
% 0.36/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['10', '19'])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      ((((sk_B) = (k1_xboole_0))
% 0.36/0.60        | ((sk_B) = (k1_xboole_0))
% 0.36/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['3', '20'])).
% 0.36/0.60  thf('22', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.36/0.60  thf('23', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t1_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.60       ( r1_tarski @ A @ C ) ))).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X2 @ X3)
% 0.36/0.60          | ~ (r1_tarski @ X3 @ X4)
% 0.36/0.60          | (r1_tarski @ X2 @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.36/0.60          | ((sk_B) = (k1_xboole_0))
% 0.36/0.60          | (r1_tarski @ sk_B @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.60  thf('27', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.36/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_B @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf(t38_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.36/0.60       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i]:
% 0.36/0.60         (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.36/0.60  thf('30', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf('31', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['30'])).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         (((X17) != (k1_xboole_0))
% 0.36/0.60          | ((k8_setfam_1 @ X18 @ X17) = (X18))
% 0.36/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      (![X18 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.36/0.60          | ((k8_setfam_1 @ X18 @ k1_xboole_0) = (X18)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.60  thf(t4_subset_1, axiom,
% 0.36/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.36/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.60  thf('35', plain, (![X18 : $i]: ((k8_setfam_1 @ X18 @ k1_xboole_0) = (X18))),
% 0.36/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(dt_k8_setfam_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.60       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.60  thf('37', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i]:
% 0.36/0.60         ((m1_subset_1 @ (k8_setfam_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.36/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.36/0.60      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.60  thf(t3_subset, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      (![X25 : $i, X26 : $i]:
% 0.36/0.60         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.60  thf('40', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.36/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.60  thf('41', plain, ($false),
% 0.36/0.60      inference('demod', [status(thm)], ['0', '31', '35', '40'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
