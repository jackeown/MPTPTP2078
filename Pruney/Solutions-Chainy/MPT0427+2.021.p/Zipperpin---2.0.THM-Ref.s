%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bk6LXC2p6O

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:23 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 127 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  479 (1346 expanded)
%              Number of equality atoms :   48 (  89 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X12 @ X11 )
        = ( k6_setfam_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('3',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k6_setfam_1 @ X16 @ X15 )
        = ( k1_setfam_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('6',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X12 @ X11 )
        = ( k6_setfam_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k6_setfam_1 @ X16 @ X15 )
        = ( k1_setfam_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('13',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_tarski @ ( k1_setfam_1 @ X23 ) @ ( k1_setfam_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('23',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ( sk_C_1 = sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    k1_xboole_0 = sk_B ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X12 @ X11 )
        = X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('32',plain,(
    ! [X12: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) )
      | ( ( k8_setfam_1 @ X12 @ k1_xboole_0 )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('34',plain,(
    ! [X12: $i] :
      ( ( k8_setfam_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','30','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('38',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('42',plain,(
    r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('44',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['35','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bk6LXC2p6O
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 177 iterations in 0.062s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.33/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.33/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.52  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.33/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.33/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.33/0.52  thf(t59_setfam_1, conjecture,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52       ( ![C:$i]:
% 0.33/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52           ( ( r1_tarski @ B @ C ) =>
% 0.33/0.52             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.33/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.52    (~( ![A:$i,B:$i]:
% 0.33/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52          ( ![C:$i]:
% 0.33/0.52            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52              ( ( r1_tarski @ B @ C ) =>
% 0.33/0.52                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.33/0.52    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.33/0.52  thf('0', plain,
% 0.33/0.52      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.33/0.52          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('1', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(d10_setfam_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.33/0.52           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.33/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.33/0.52  thf('2', plain,
% 0.33/0.52      (![X11 : $i, X12 : $i]:
% 0.33/0.52         (((X11) = (k1_xboole_0))
% 0.33/0.52          | ((k8_setfam_1 @ X12 @ X11) = (k6_setfam_1 @ X12 @ X11))
% 0.33/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.33/0.52      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.33/0.52  thf('3', plain,
% 0.33/0.52      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.33/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.33/0.52  thf('4', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(redefinition_k6_setfam_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.33/0.52  thf('5', plain,
% 0.33/0.52      (![X15 : $i, X16 : $i]:
% 0.33/0.52         (((k6_setfam_1 @ X16 @ X15) = (k1_setfam_1 @ X15))
% 0.33/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.33/0.52      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.33/0.52  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.33/0.52  thf('7', plain,
% 0.33/0.52      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.33/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.33/0.52      inference('demod', [status(thm)], ['3', '6'])).
% 0.33/0.52  thf('8', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('9', plain,
% 0.33/0.52      (![X11 : $i, X12 : $i]:
% 0.33/0.52         (((X11) = (k1_xboole_0))
% 0.33/0.52          | ((k8_setfam_1 @ X12 @ X11) = (k6_setfam_1 @ X12 @ X11))
% 0.33/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.33/0.52      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.33/0.52  thf('10', plain,
% 0.33/0.52      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.33/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.33/0.52  thf('11', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('12', plain,
% 0.33/0.52      (![X15 : $i, X16 : $i]:
% 0.33/0.52         (((k6_setfam_1 @ X16 @ X15) = (k1_setfam_1 @ X15))
% 0.33/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.33/0.52      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.33/0.52  thf('13', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.33/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.33/0.52  thf('14', plain,
% 0.33/0.52      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.33/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.33/0.52      inference('demod', [status(thm)], ['10', '13'])).
% 0.33/0.52  thf('15', plain,
% 0.33/0.52      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.33/0.52          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('16', plain,
% 0.33/0.52      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.33/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.33/0.52  thf('17', plain,
% 0.33/0.52      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.33/0.52        | ((sk_C_1) = (k1_xboole_0))
% 0.33/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['7', '16'])).
% 0.33/0.52  thf('18', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(t7_setfam_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.33/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.33/0.52         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.33/0.52  thf('19', plain,
% 0.33/0.52      (![X22 : $i, X23 : $i]:
% 0.33/0.52         (((X22) = (k1_xboole_0))
% 0.33/0.52          | ~ (r1_tarski @ X22 @ X23)
% 0.33/0.52          | (r1_tarski @ (k1_setfam_1 @ X23) @ (k1_setfam_1 @ X22)))),
% 0.33/0.52      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.33/0.52  thf('20', plain,
% 0.33/0.52      (((r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.33/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.33/0.52  thf('21', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.33/0.52      inference('clc', [status(thm)], ['17', '20'])).
% 0.33/0.52  thf('22', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.33/0.52      inference('clc', [status(thm)], ['17', '20'])).
% 0.33/0.52  thf('23', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(d10_xboole_0, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.33/0.52  thf('24', plain,
% 0.33/0.52      (![X0 : $i, X2 : $i]:
% 0.33/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.33/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.33/0.52  thf('25', plain, ((~ (r1_tarski @ sk_C_1 @ sk_B) | ((sk_C_1) = (sk_B)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.33/0.52  thf('26', plain,
% 0.33/0.52      ((~ (r1_tarski @ k1_xboole_0 @ sk_B)
% 0.33/0.52        | ((sk_B) = (k1_xboole_0))
% 0.33/0.52        | ((sk_C_1) = (sk_B)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['22', '25'])).
% 0.33/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.33/0.52  thf('27', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.33/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.33/0.52  thf('28', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_1) = (sk_B)))),
% 0.33/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.33/0.52  thf('29', plain,
% 0.33/0.52      ((((k1_xboole_0) = (sk_B))
% 0.33/0.52        | ((sk_B) = (k1_xboole_0))
% 0.33/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.33/0.52      inference('sup+', [status(thm)], ['21', '28'])).
% 0.33/0.52  thf('30', plain, (((k1_xboole_0) = (sk_B))),
% 0.33/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.33/0.52  thf('31', plain,
% 0.33/0.52      (![X11 : $i, X12 : $i]:
% 0.33/0.52         (((X11) != (k1_xboole_0))
% 0.33/0.52          | ((k8_setfam_1 @ X12 @ X11) = (X12))
% 0.33/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.33/0.52      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.33/0.52  thf('32', plain,
% 0.33/0.52      (![X12 : $i]:
% 0.33/0.52         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12)))
% 0.33/0.52          | ((k8_setfam_1 @ X12 @ k1_xboole_0) = (X12)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.33/0.52  thf(t4_subset_1, axiom,
% 0.33/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.33/0.52  thf('33', plain,
% 0.33/0.52      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.33/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.33/0.52  thf('34', plain, (![X12 : $i]: ((k8_setfam_1 @ X12 @ k1_xboole_0) = (X12))),
% 0.33/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.33/0.52  thf('35', plain, (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.33/0.52      inference('demod', [status(thm)], ['0', '30', '34'])).
% 0.33/0.52  thf('36', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(dt_k8_setfam_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.33/0.52  thf('37', plain,
% 0.33/0.52      (![X13 : $i, X14 : $i]:
% 0.33/0.52         ((m1_subset_1 @ (k8_setfam_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.33/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.33/0.52      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.33/0.52  thf('38', plain,
% 0.33/0.52      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.33/0.52  thf(t2_subset, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.33/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.33/0.52  thf('39', plain,
% 0.33/0.52      (![X17 : $i, X18 : $i]:
% 0.33/0.52         ((r2_hidden @ X17 @ X18)
% 0.33/0.52          | (v1_xboole_0 @ X18)
% 0.33/0.52          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.33/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.33/0.52  thf('40', plain,
% 0.33/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.33/0.52        | (r2_hidden @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.33/0.52  thf(fc1_subset_1, axiom,
% 0.33/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.33/0.52  thf('41', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.33/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.33/0.52  thf('42', plain,
% 0.33/0.52      ((r2_hidden @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.52      inference('clc', [status(thm)], ['40', '41'])).
% 0.33/0.52  thf(d1_zfmisc_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.33/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.33/0.52  thf('43', plain,
% 0.33/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X7 @ X6)
% 0.33/0.52          | (r1_tarski @ X7 @ X5)
% 0.33/0.52          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.33/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.33/0.52  thf('44', plain,
% 0.33/0.52      (![X5 : $i, X7 : $i]:
% 0.33/0.52         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.33/0.52  thf('45', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.33/0.52      inference('sup-', [status(thm)], ['42', '44'])).
% 0.33/0.52  thf('46', plain, ($false), inference('demod', [status(thm)], ['35', '45'])).
% 0.33/0.52  
% 0.33/0.52  % SZS output end Refutation
% 0.33/0.52  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
