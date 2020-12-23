%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sb5GODkRi9

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 104 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  495 (1425 expanded)
%              Number of equality atoms :    6 (  38 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t44_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X9: $i] :
      ( ~ ( r2_hidden @ X9 @ sk_C )
      | ( r2_hidden @ X9 @ sk_B )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X9: $i] :
      ( ~ ( r2_hidden @ X9 @ sk_B )
      | ( r2_hidden @ X9 @ sk_C )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['23','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sb5GODkRi9
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 36 iterations in 0.023s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(t44_setfam_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48           ( ( ![D:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.48             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48          ( ![C:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48              ( ( ![D:$i]:
% 0.21/0.48                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.48                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t7_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48           ( ( ![D:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.48                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.48             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.48          | (r1_tarski @ X5 @ X3)
% 0.21/0.48          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.21/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.48          | (r2_hidden @ (sk_D @ sk_B @ X0 @ (k1_zfmisc_1 @ sk_A)) @ X0)
% 0.21/0.48          | (r1_tarski @ X0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((r1_tarski @ sk_C @ sk_B)
% 0.21/0.48        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ (k1_zfmisc_1 @ sk_A)) @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t4_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.48       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.48          | (m1_subset_1 @ X6 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((r1_tarski @ sk_C @ sk_B)
% 0.21/0.48        | (m1_subset_1 @ (sk_D @ sk_B @ sk_C @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.48           (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X9 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X9 @ sk_C)
% 0.21/0.48          | (r2_hidden @ X9 @ sk_B)
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((r1_tarski @ sk_C @ sk_B)
% 0.21/0.48        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.21/0.48        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_C @ (k1_zfmisc_1 @ sk_A)) @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((r1_tarski @ sk_C @ sk_B)
% 0.21/0.48        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ (k1_zfmisc_1 @ sk_A)) @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((r2_hidden @ (sk_D @ sk_B @ sk_C @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.21/0.48        | (r1_tarski @ sk_C @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.48          | (r1_tarski @ X5 @ X3)
% 0.21/0.48          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.21/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.48          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.21/0.48          | (r1_tarski @ X0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((r1_tarski @ sk_C @ sk_B)
% 0.21/0.48        | (r1_tarski @ sk_C @ sk_B)
% 0.21/0.48        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain, (((r1_tarski @ sk_C @ sk_B) | (r1_tarski @ sk_C @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i]:
% 0.21/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('21', plain, ((~ (r1_tarski @ sk_B @ sk_C) | ((sk_B) = (sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, (((sk_B) != (sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.48          | (r1_tarski @ X5 @ X3)
% 0.21/0.48          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.21/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.48          | (r2_hidden @ (sk_D @ sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ X0)
% 0.21/0.48          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.48        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.48          | (m1_subset_1 @ X6 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.48        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.48           (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X9 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X9 @ sk_B)
% 0.21/0.48          | (r2_hidden @ X9 @ sk_C)
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.48        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C)
% 0.21/0.48        | ~ (r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.48        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C)
% 0.21/0.48        | (r1_tarski @ sk_B @ sk_C))),
% 0.21/0.48      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.48          | (r1_tarski @ X5 @ X3)
% 0.21/0.48          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.21/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.48          | ~ (r2_hidden @ (sk_D @ sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_C)
% 0.21/0.48          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.48        | (r1_tarski @ sk_B @ sk_C)
% 0.21/0.48        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('42', plain, (((r1_tarski @ sk_B @ sk_C) | (r1_tarski @ sk_B @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.48  thf('44', plain, ($false), inference('demod', [status(thm)], ['23', '43'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
