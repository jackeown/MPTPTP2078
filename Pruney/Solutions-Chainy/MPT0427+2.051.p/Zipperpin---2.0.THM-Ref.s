%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CNhlbj1UgZ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 241 expanded)
%              Number of leaves         :   20 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  493 (2734 expanded)
%              Number of equality atoms :   49 ( 184 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( r1_xboole_0 @ X5 @ X5 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ ( k1_setfam_1 @ X17 ) @ ( k1_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('5',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X8 @ X7 )
        = ( k6_setfam_1 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('8',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k6_setfam_1 @ X12 @ X11 )
        = ( k1_setfam_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('11',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X8 @ X7 )
        = ( k6_setfam_1 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('15',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k6_setfam_1 @ X12 @ X11 )
        = ( k1_setfam_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_B @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','28'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('36',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','35'])).

thf('40',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X8 @ X7 )
        = X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('42',plain,(
    ! [X8: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) )
      | ( ( k8_setfam_1 @ X8 @ k1_xboole_0 )
        = X8 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('46',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['37','43','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CNhlbj1UgZ
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:21:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 100 iterations in 0.041s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.19/0.49  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(t59_setfam_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.49           ( ( r1_tarski @ B @ C ) =>
% 0.19/0.49             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.49          ( ![C:$i]:
% 0.19/0.49            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.49              ( ( r1_tarski @ B @ C ) =>
% 0.19/0.49                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t66_xboole_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.19/0.49       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X5 : $i]: ((r1_xboole_0 @ X5 @ X5) | ((X5) != (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.49  thf('2', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.49  thf('3', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t7_setfam_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i]:
% 0.19/0.49         (((X16) = (k1_xboole_0))
% 0.19/0.49          | ~ (r1_tarski @ X16 @ X17)
% 0.19/0.49          | (r1_tarski @ (k1_setfam_1 @ X17) @ (k1_setfam_1 @ X16)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d10_setfam_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.49       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.49           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.19/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i]:
% 0.19/0.49         (((X7) = (k1_xboole_0))
% 0.19/0.49          | ((k8_setfam_1 @ X8 @ X7) = (k6_setfam_1 @ X8 @ X7))
% 0.19/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.19/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k6_setfam_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.49       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]:
% 0.19/0.49         (((k6_setfam_1 @ X12 @ X11) = (k1_setfam_1 @ X11))
% 0.19/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.19/0.49  thf('11', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.19/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.19/0.49      inference('demod', [status(thm)], ['8', '11'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i]:
% 0.19/0.49         (((X7) = (k1_xboole_0))
% 0.19/0.49          | ((k8_setfam_1 @ X8 @ X7) = (k6_setfam_1 @ X8 @ X7))
% 0.19/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]:
% 0.19/0.49         (((k6_setfam_1 @ X12 @ X11) = (k1_setfam_1 @ X11))
% 0.19/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.19/0.49  thf('18', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.19/0.49        | ((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['12', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      ((((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '22'])).
% 0.19/0.49  thf('24', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.49  thf('25', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t63_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.19/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X2 @ X3)
% 0.19/0.49          | ~ (r1_xboole_0 @ X3 @ X4)
% 0.19/0.49          | (r1_xboole_0 @ X2 @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.49          | ((sk_B) = (k1_xboole_0))
% 0.19/0.49          | (r1_xboole_0 @ sk_B @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (((r1_xboole_0 @ sk_B @ k1_xboole_0) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '28'])).
% 0.19/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      ((((sk_B) = (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.49          | ((sk_B) = (k1_xboole_0))
% 0.19/0.49          | (r1_xboole_0 @ sk_B @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      ((((sk_B) = (k1_xboole_0))
% 0.19/0.49        | (r1_xboole_0 @ sk_B @ sk_B)
% 0.19/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.49  thf('34', plain, (((r1_xboole_0 @ sk_B @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.49  thf('36', plain, (((sk_B) = (k1_xboole_0))),
% 0.19/0.49      inference('clc', [status(thm)], ['34', '35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.19/0.49          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '36'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('39', plain, (((sk_B) = (k1_xboole_0))),
% 0.19/0.49      inference('clc', [status(thm)], ['34', '35'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i]:
% 0.19/0.49         (((X7) != (k1_xboole_0))
% 0.19/0.49          | ((k8_setfam_1 @ X8 @ X7) = (X8))
% 0.19/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X8 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8)))
% 0.19/0.49          | ((k8_setfam_1 @ X8 @ k1_xboole_0) = (X8)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.19/0.49  thf('43', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['40', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_k8_setfam_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.49       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X9 : $i, X10 : $i]:
% 0.19/0.49         ((m1_subset_1 @ (k8_setfam_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.19/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.49  thf(t3_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i]:
% 0.19/0.49         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.49  thf('48', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.19/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.49  thf('49', plain, ($false),
% 0.19/0.49      inference('demod', [status(thm)], ['37', '43', '48'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
