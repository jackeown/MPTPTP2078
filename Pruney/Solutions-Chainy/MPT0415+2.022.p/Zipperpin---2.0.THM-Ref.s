%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j98A3CnhYd

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 133 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  463 (1263 expanded)
%              Number of equality atoms :   27 ( 113 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ ( sk_D @ X12 @ X14 @ X13 ) ) @ X14 )
      | ( X12
        = ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_setfam_1 @ X17 @ ( k7_setfam_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('11',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( X12
       != ( k7_setfam_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ X15 ) @ X14 )
      | ~ ( r2_hidden @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X15 @ ( k7_setfam_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X9 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X8 @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X8 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['29','32'])).

thf('34',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['8','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['29','32'])).

thf('36',plain,(
    $false ),
    inference('sup-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j98A3CnhYd
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 80 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(t46_setfam_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d8_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.21/0.49             ( ![D:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49                 ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.21/0.49          | (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.21/0.49          | (r2_hidden @ (k3_subset_1 @ X13 @ (sk_D @ X12 @ X14 @ X13)) @ X14)
% 0.21/0.49          | ((X12) = (k7_setfam_1 @ X13 @ X14))
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.49          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.21/0.49          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A)) @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.49        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.49           sk_B)
% 0.21/0.49        | ((sk_B) = (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.49  thf('5', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.49        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.49           sk_B)
% 0.21/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.49        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.49           sk_B))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(involutiveness_k7_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (((k7_setfam_1 @ X17 @ (k7_setfam_1 @ X17 @ X16)) = (X16))
% 0.21/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.21/0.49      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.21/0.49          | ((X12) != (k7_setfam_1 @ X13 @ X14))
% 0.21/0.49          | (r2_hidden @ (k3_subset_1 @ X13 @ X15) @ X14)
% 0.21/0.49          | ~ (r2_hidden @ X15 @ X12)
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13))
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13))
% 0.21/0.49          | ~ (r2_hidden @ X15 @ (k7_setfam_1 @ X13 @ X14))
% 0.21/0.49          | (r2_hidden @ (k3_subset_1 @ X13 @ X15) @ X14)
% 0.21/0.49          | ~ (m1_subset_1 @ (k7_setfam_1 @ X13 @ X14) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.49          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.49          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf(t4_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.21/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.49  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.49  thf(t100_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.49           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf(t64_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (((X7) != (X9))
% 0.21/0.49          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X8 @ (k1_tarski @ X9))))),
% 0.21/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X8 @ (k1_tarski @ X9)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ~ (r2_hidden @ X0 @ 
% 0.21/0.49            (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.49  thf(t92_xboole_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('27', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.49  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['20', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t4_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X20 @ X21)
% 0.21/0.49          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.21/0.49          | (m1_subset_1 @ X20 @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['29', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['8', '33'])).
% 0.21/0.49  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['29', '32'])).
% 0.21/0.49  thf('36', plain, ($false), inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
