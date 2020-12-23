%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BJRkZMqYLg

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:15 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  468 (1164 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ X10 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X10 @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ X14 ) @ ( k7_setfam_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ X10 @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X15 @ X14 ) @ ( k7_setfam_1 @ X15 @ X16 ) )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('31',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BJRkZMqYLg
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 196 iterations in 0.102s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.55  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(t51_setfam_1, conjecture,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.55       ( ![C:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.55           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.35/0.56             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.35/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.56    (~( ![A:$i,B:$i]:
% 0.35/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.56          ( ![C:$i]:
% 0.35/0.56            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.56              ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.35/0.56                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.35/0.56    inference('cnf.neg', [status(esa)], [t51_setfam_1])).
% 0.35/0.56  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('1', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('2', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(t7_subset_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.56       ( ![C:$i]:
% 0.35/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.56           ( ( ![D:$i]:
% 0.35/0.56               ( ( m1_subset_1 @ D @ A ) =>
% 0.35/0.56                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.35/0.56             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.35/0.56  thf('3', plain,
% 0.35/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.35/0.56          | (r1_tarski @ X10 @ X8)
% 0.35/0.56          | (m1_subset_1 @ (sk_D @ X8 @ X10 @ X9) @ X9)
% 0.35/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.35/0.56  thf('4', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.35/0.56          | (m1_subset_1 @ (sk_D @ sk_C_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.35/0.56             (k1_zfmisc_1 @ sk_A))
% 0.35/0.56          | (r1_tarski @ X0 @ sk_C_1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.56  thf('5', plain,
% 0.35/0.56      (((r1_tarski @ sk_B @ sk_C_1)
% 0.35/0.56        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.35/0.56           (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.35/0.56  thf('6', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('7', plain,
% 0.35/0.56      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.35/0.56        (k1_zfmisc_1 @ sk_A))),
% 0.35/0.56      inference('clc', [status(thm)], ['5', '6'])).
% 0.35/0.56  thf('8', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(t49_setfam_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.56       ( ![C:$i]:
% 0.35/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.56           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.35/0.56             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.35/0.56  thf('9', plain,
% 0.35/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.35/0.56          | ~ (r2_hidden @ X14 @ X16)
% 0.35/0.56          | (r2_hidden @ (k3_subset_1 @ X15 @ X14) @ (k7_setfam_1 @ X15 @ X16))
% 0.35/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.35/0.56      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.35/0.56  thf('10', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.35/0.56          | ~ (r2_hidden @ X0 @ sk_B)
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.56  thf('11', plain,
% 0.35/0.56      ((~ (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.35/0.56        | (r2_hidden @ 
% 0.35/0.56           (k3_subset_1 @ sk_A @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.35/0.56           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['7', '10'])).
% 0.35/0.56  thf('12', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('13', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('14', plain,
% 0.35/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.35/0.56          | (r1_tarski @ X10 @ X8)
% 0.35/0.56          | (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.35/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.35/0.56  thf('15', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.35/0.56          | (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) @ X0)
% 0.35/0.56          | (r1_tarski @ X0 @ sk_C_1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.56  thf('16', plain,
% 0.35/0.56      (((r1_tarski @ sk_B @ sk_C_1)
% 0.35/0.56        | (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B))),
% 0.35/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.35/0.56  thf('17', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('18', plain,
% 0.35/0.56      ((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B)),
% 0.35/0.56      inference('clc', [status(thm)], ['16', '17'])).
% 0.35/0.56  thf('19', plain,
% 0.35/0.56      ((r2_hidden @ 
% 0.35/0.56        (k3_subset_1 @ sk_A @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.35/0.56        (k7_setfam_1 @ sk_A @ sk_B))),
% 0.35/0.56      inference('demod', [status(thm)], ['11', '18'])).
% 0.35/0.56  thf('20', plain,
% 0.35/0.56      ((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ (k7_setfam_1 @ sk_A @ sk_C_1))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(t3_subset, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.56  thf('21', plain,
% 0.35/0.56      (![X11 : $i, X13 : $i]:
% 0.35/0.56         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.35/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.56  thf('22', plain,
% 0.35/0.56      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k7_setfam_1 @ sk_A @ sk_C_1)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.56  thf(l3_subset_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.35/0.56  thf('23', plain,
% 0.35/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X5 @ X6)
% 0.35/0.56          | (r2_hidden @ X5 @ X7)
% 0.35/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.35/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.35/0.56  thf('24', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_C_1))
% 0.35/0.56          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.56  thf('25', plain,
% 0.35/0.56      ((r2_hidden @ 
% 0.35/0.56        (k3_subset_1 @ sk_A @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.35/0.56        (k7_setfam_1 @ sk_A @ sk_C_1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['19', '24'])).
% 0.35/0.56  thf('26', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('27', plain,
% 0.35/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.35/0.56          | ~ (r2_hidden @ (k3_subset_1 @ X15 @ X14) @ 
% 0.35/0.56               (k7_setfam_1 @ X15 @ X16))
% 0.35/0.56          | (r2_hidden @ X14 @ X16)
% 0.35/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.35/0.56      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.35/0.56  thf('28', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((r2_hidden @ X0 @ sk_C_1)
% 0.35/0.56          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.35/0.56               (k7_setfam_1 @ sk_A @ sk_C_1))
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.56  thf('29', plain,
% 0.35/0.56      ((~ (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.35/0.56           (k1_zfmisc_1 @ sk_A))
% 0.35/0.56        | (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C_1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['25', '28'])).
% 0.35/0.56  thf('30', plain,
% 0.35/0.56      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.35/0.56        (k1_zfmisc_1 @ sk_A))),
% 0.35/0.56      inference('clc', [status(thm)], ['5', '6'])).
% 0.35/0.56  thf('31', plain,
% 0.35/0.56      ((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C_1)),
% 0.35/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.56  thf('32', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('33', plain,
% 0.35/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.35/0.56          | (r1_tarski @ X10 @ X8)
% 0.35/0.56          | ~ (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X8)
% 0.35/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.35/0.56  thf('34', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.35/0.56          | ~ (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_C_1)
% 0.35/0.56          | (r1_tarski @ X0 @ sk_C_1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.56  thf('35', plain,
% 0.35/0.56      (((r1_tarski @ sk_B @ sk_C_1)
% 0.35/0.56        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.35/0.56      inference('sup-', [status(thm)], ['31', '34'])).
% 0.35/0.56  thf('36', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('37', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.35/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.35/0.56  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.35/0.56  
% 0.35/0.56  % SZS output end Refutation
% 0.35/0.56  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
