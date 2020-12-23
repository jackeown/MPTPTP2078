%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0XuLT6c4Xp

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:34 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  178 ( 221 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t5_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ A )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k1_setfam_1 @ A )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t5_setfam_1])).

thf('0',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ( X7
        = ( k1_setfam_1 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ X3 )
        = X3 )
      | ~ ( r2_hidden @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_setfam_1 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    ( k1_setfam_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ X3 )
        = X3 )
      | ~ ( r2_hidden @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0XuLT6c4Xp
% 0.14/0.36  % Computer   : n013.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:38:40 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 21 iterations in 0.018s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.50  thf(t5_setfam_1, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.23/0.50       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.23/0.50          ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t5_setfam_1])).
% 0.23/0.50  thf('0', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d1_setfam_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.23/0.50         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.50       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.23/0.50         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.23/0.50           ( ![C:$i]:
% 0.23/0.50             ( ( r2_hidden @ C @ B ) <=>
% 0.23/0.50               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.50         ((r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.23/0.50          | (r2_hidden @ (sk_C @ X7 @ X8) @ X9)
% 0.23/0.50          | ~ (r2_hidden @ X9 @ X8)
% 0.23/0.50          | ((X7) = (k1_setfam_1 @ X8))
% 0.23/0.50          | ((X8) = (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((sk_A) = (k1_xboole_0))
% 0.23/0.50          | ((X0) = (k1_setfam_1 @ sk_A))
% 0.23/0.50          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0)
% 0.23/0.50          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf('3', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(l22_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( r2_hidden @ A @ B ) =>
% 0.23/0.50       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         (((k2_xboole_0 @ (k1_tarski @ X4) @ X3) = (X3))
% 0.23/0.50          | ~ (r2_hidden @ X4 @ X3))),
% 0.23/0.50      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (((k2_xboole_0 @ (k1_tarski @ k1_xboole_0) @ sk_A) = (sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf(t49_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X5 : $i, X6 : $i]:
% 0.23/0.50         ((k2_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.23/0.50  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((X0) = (k1_setfam_1 @ sk_A))
% 0.23/0.50          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0)
% 0.23/0.50          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ X0))),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['2', '7'])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.50        | ((k1_xboole_0) = (k1_setfam_1 @ sk_A)))),
% 0.23/0.50      inference('eq_fact', [status(thm)], ['8'])).
% 0.23/0.50  thf('10', plain, (((k1_setfam_1 @ sk_A) != (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('11', plain, ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0)),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         (((k2_xboole_0 @ (k1_tarski @ X4) @ X3) = (X3))
% 0.23/0.50          | ~ (r2_hidden @ X4 @ X3))),
% 0.23/0.50      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (((k2_xboole_0 @ (k1_tarski @ (sk_C @ k1_xboole_0 @ sk_A)) @ k1_xboole_0)
% 0.23/0.50         = (k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X5 : $i, X6 : $i]:
% 0.23/0.50         ((k2_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.23/0.50  thf('15', plain, ($false),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
