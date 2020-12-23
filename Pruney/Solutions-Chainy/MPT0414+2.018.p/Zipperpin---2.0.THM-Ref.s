%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eFiVkoRbng

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 167 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  419 (2248 expanded)
%              Number of equality atoms :    6 (  64 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_C_1 )
      | ( r2_hidden @ X11 @ sk_B )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('22',plain,
    ( ( sk_C_1 = sk_B )
    | ( r2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('26',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_B )
      | ( r2_hidden @ X11 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('34',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('36',plain,(
    ~ ( r2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eFiVkoRbng
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 58 iterations in 0.035s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(t44_setfam_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.50           ( ( ![D:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.50             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.50          ( ![C:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.50              ( ( ![D:$i]:
% 0.22/0.50                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.50                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t7_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50           ( ( ![D:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ D @ A ) =>
% 0.22/0.50                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.50             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.22/0.50          | (r1_tarski @ X7 @ X5)
% 0.22/0.50          | (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X7)
% 0.22/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.22/0.50          | (r2_hidden @ (sk_D @ sk_B @ X0 @ (k1_zfmisc_1 @ sk_A)) @ X0)
% 0.22/0.50          | (r1_tarski @ X0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.22/0.50        | (r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)) @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.22/0.50          | (r1_tarski @ X7 @ X5)
% 0.22/0.50          | (m1_subset_1 @ (sk_D @ X5 @ X7 @ X6) @ X6)
% 0.22/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.22/0.50          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.22/0.50             (k1_zfmisc_1 @ sk_A))
% 0.22/0.50          | (r1_tarski @ X0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.22/0.50        | (m1_subset_1 @ (sk_D @ sk_B @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.22/0.50           (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X11 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X11 @ sk_C_1)
% 0.22/0.50          | (r2_hidden @ X11 @ sk_B)
% 0.22/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.22/0.50        | (r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.22/0.50        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)) @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.22/0.50        | (r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.22/0.50        | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (((r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.22/0.50        | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.22/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.22/0.50          | (r1_tarski @ X7 @ X5)
% 0.22/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X5)
% 0.22/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.22/0.50          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.22/0.50          | (r1_tarski @ X0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.22/0.50        | (r1_tarski @ sk_C_1 @ sk_B)
% 0.22/0.50        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (((r1_tarski @ sk_C_1 @ sk_B) | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.22/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.50  thf(d8_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.22/0.50       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i]:
% 0.22/0.50         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.50  thf('22', plain, ((((sk_C_1) = (sk_B)) | (r2_xboole_0 @ sk_C_1 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain, (((sk_B) != (sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, ((r2_xboole_0 @ sk_C_1 @ sk_B)),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf(t6_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.22/0.50          ( ![C:$i]:
% 0.22/0.50            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (r2_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.22/0.50  thf('26', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t4_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X8 @ X9)
% 0.22/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.22/0.50          | (m1_subset_1 @ X8 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((m1_subset_1 @ (sk_C @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X11 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X11 @ sk_B)
% 0.22/0.50          | (r2_hidden @ X11 @ sk_C_1)
% 0.22/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)
% 0.22/0.50        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('34', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (r2_xboole_0 @ X3 @ X4) | ~ (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.22/0.50  thf('36', plain, (~ (r2_xboole_0 @ sk_C_1 @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain, ((r2_xboole_0 @ sk_C_1 @ sk_B)),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('38', plain, ($false), inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
