%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lNXjp3PPqU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:15 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   49 (  81 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  378 ( 763 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t51_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
             => ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ X12 ) @ ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k7_setfam_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k7_setfam_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X13 @ X12 ) @ ( k7_setfam_1 @ X13 @ X14 ) )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_2 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
    | ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lNXjp3PPqU
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 13:00:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 311 iterations in 0.257s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.50/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.72  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.50/0.72  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.50/0.72  thf(t51_setfam_1, conjecture,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.72       ( ![C:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.72           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.50/0.72             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i,B:$i]:
% 0.50/0.72        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.72          ( ![C:$i]:
% 0.50/0.72            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.72              ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.50/0.72                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t51_setfam_1])).
% 0.50/0.72  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_C_2)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(d3_tarski, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.72  thf('1', plain,
% 0.50/0.72      (![X1 : $i, X3 : $i]:
% 0.50/0.72         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('2', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t3_subset, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.72  thf('3', plain,
% 0.50/0.72      (![X9 : $i, X10 : $i]:
% 0.50/0.72         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.50/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.72  thf('4', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('5', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.72          | (r2_hidden @ X0 @ X2)
% 0.50/0.72          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.50/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.72  thf('7', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B @ X0)
% 0.50/0.72          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['1', '6'])).
% 0.50/0.72  thf(d1_zfmisc_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.50/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.50/0.72  thf('8', plain,
% 0.50/0.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X7 @ X6)
% 0.50/0.72          | (r1_tarski @ X7 @ X5)
% 0.50/0.72          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.50/0.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.50/0.72  thf('9', plain,
% 0.50/0.72      (![X5 : $i, X7 : $i]:
% 0.50/0.72         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.50/0.72      inference('simplify', [status(thm)], ['8'])).
% 0.50/0.72  thf('10', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B @ X0) | (r1_tarski @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['7', '9'])).
% 0.50/0.72  thf('11', plain,
% 0.50/0.72      (![X9 : $i, X11 : $i]:
% 0.50/0.72         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.50/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.72  thf('12', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B @ X0)
% 0.50/0.72          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t49_setfam_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.72       ( ![C:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.50/0.72             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.50/0.72  thf('14', plain,
% 0.50/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.50/0.72          | ~ (r2_hidden @ X12 @ X14)
% 0.50/0.72          | (r2_hidden @ (k3_subset_1 @ X13 @ X12) @ (k7_setfam_1 @ X13 @ X14))
% 0.50/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.50/0.72      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.50/0.72  thf('15', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.50/0.72          | ~ (r2_hidden @ X0 @ sk_B)
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.50/0.72  thf('16', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B @ X0)
% 0.50/0.72          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)
% 0.50/0.72          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.72             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['12', '15'])).
% 0.50/0.72  thf('17', plain,
% 0.50/0.72      (![X1 : $i, X3 : $i]:
% 0.50/0.72         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('18', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.72           (k7_setfam_1 @ sk_A @ sk_B))
% 0.50/0.72          | (r1_tarski @ sk_B @ X0))),
% 0.50/0.72      inference('clc', [status(thm)], ['16', '17'])).
% 0.50/0.72  thf('19', plain,
% 0.50/0.72      ((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ (k7_setfam_1 @ sk_A @ sk_C_2))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('20', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.72          | (r2_hidden @ X0 @ X2)
% 0.50/0.72          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('21', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_C_2))
% 0.50/0.72          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['19', '20'])).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B @ X0)
% 0.50/0.72          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.72             (k7_setfam_1 @ sk_A @ sk_C_2)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['18', '21'])).
% 0.50/0.72  thf('23', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.50/0.72          | ~ (r2_hidden @ (k3_subset_1 @ X13 @ X12) @ 
% 0.50/0.72               (k7_setfam_1 @ X13 @ X14))
% 0.50/0.72          | (r2_hidden @ X12 @ X14)
% 0.50/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.50/0.72      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.50/0.72  thf('25', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ X0 @ sk_C_2)
% 0.50/0.72          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.50/0.72               (k7_setfam_1 @ sk_A @ sk_C_2))
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.72  thf('26', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B @ X0)
% 0.50/0.72          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.50/0.72          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_2))),
% 0.50/0.72      inference('sup-', [status(thm)], ['22', '25'])).
% 0.50/0.72  thf('27', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B @ X0)
% 0.50/0.72          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.50/0.72  thf('28', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_2) | (r1_tarski @ sk_B @ X0))),
% 0.50/0.72      inference('clc', [status(thm)], ['26', '27'])).
% 0.50/0.72  thf('29', plain,
% 0.50/0.72      (![X1 : $i, X3 : $i]:
% 0.50/0.72         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('30', plain,
% 0.50/0.72      (((r1_tarski @ sk_B @ sk_C_2) | (r1_tarski @ sk_B @ sk_C_2))),
% 0.50/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.72  thf('31', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 0.50/0.72      inference('simplify', [status(thm)], ['30'])).
% 0.50/0.72  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.50/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
