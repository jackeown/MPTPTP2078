%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V3eEqDjOcJ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  90 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  444 (1140 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ ( k3_subset_1 @ X8 @ X7 ) @ ( k7_setfam_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X8 @ X7 ) @ ( k7_setfam_1 @ X8 @ X9 ) )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('29',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V3eEqDjOcJ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 36 iterations in 0.027s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(t51_setfam_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.21/0.49             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49              ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.21/0.49                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t51_setfam_1])).
% 0.21/0.49  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t7_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49           ( ( ![D:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.49                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.49             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.49          | (r1_tarski @ X6 @ X4)
% 0.21/0.49          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ X5)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.49          | (m1_subset_1 @ (sk_D @ sk_C_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.49             (k1_zfmisc_1 @ sk_A))
% 0.21/0.49          | (r1_tarski @ X0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ sk_C_1)
% 0.21/0.49        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.49           (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.49  thf('6', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.49        (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t49_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.21/0.49             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.49          | ~ (r2_hidden @ X7 @ X9)
% 0.21/0.49          | (r2_hidden @ (k3_subset_1 @ X8 @ X7) @ (k7_setfam_1 @ X8 @ X9))
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((~ (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.21/0.49        | (r2_hidden @ 
% 0.21/0.49           (k3_subset_1 @ sk_A @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.49           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.49          | (r1_tarski @ X6 @ X4)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.49          | (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) @ X0)
% 0.21/0.49          | (r1_tarski @ X0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ sk_C_1)
% 0.21/0.49        | (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.49  thf('17', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((r2_hidden @ 
% 0.21/0.49        (k3_subset_1 @ sk_A @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.49        (k7_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ (k7_setfam_1 @ sk_A @ sk_C_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d3_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | (r2_hidden @ X0 @ X2)
% 0.21/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_C_1))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((r2_hidden @ 
% 0.21/0.49        (k3_subset_1 @ sk_A @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.49        (k7_setfam_1 @ sk_A @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.49          | ~ (r2_hidden @ (k3_subset_1 @ X8 @ X7) @ (k7_setfam_1 @ X8 @ X9))
% 0.21/0.49          | (r2_hidden @ X7 @ X9)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ X0 @ sk_C_1)
% 0.21/0.49          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.21/0.49               (k7_setfam_1 @ sk_A @ sk_C_1))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.49           (k1_zfmisc_1 @ sk_A))
% 0.21/0.49        | (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.49        (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.49          | (r1_tarski @ X6 @ X4)
% 0.21/0.49          | ~ (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X4)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.49          | ~ (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_C_1)
% 0.21/0.49          | (r1_tarski @ X0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ sk_C_1)
% 0.21/0.49        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
