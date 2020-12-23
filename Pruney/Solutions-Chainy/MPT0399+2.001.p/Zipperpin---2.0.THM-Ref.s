%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XLLYYBN785

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  155 ( 167 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('1',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r1_setfam_1 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t140_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ ( k1_tarski @ X4 ) ) @ ( k1_tarski @ X4 ) )
        = X3 )
      | ~ ( r2_hidden @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t140_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k4_xboole_0 @ X3 @ ( k1_tarski @ X4 ) ) )
        = X3 )
      | ~ ( r2_hidden @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) @ ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XLLYYBN785
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 18 iterations in 0.012s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.45  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.45  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.45  thf(t7_xboole_0, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.45          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.45  thf(t21_setfam_1, conjecture,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]:
% 0.21/0.45        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.21/0.45  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(d2_setfam_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.45       ( ![C:$i]:
% 0.21/0.45         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.45              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.45         ((r2_hidden @ (sk_D @ X7 @ X8) @ X8)
% 0.21/0.45          | ~ (r2_hidden @ X7 @ X9)
% 0.21/0.45          | ~ (r1_setfam_1 @ X9 @ X8))),
% 0.21/0.45      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.45          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      ((((sk_A) = (k1_xboole_0))
% 0.21/0.45        | (r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.45  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      ((r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.45  thf(t140_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.45       ( ( k2_xboole_0 @
% 0.21/0.45           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.21/0.45         ( B ) ) ))).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X3 : $i, X4 : $i]:
% 0.21/0.45         (((k2_xboole_0 @ (k4_xboole_0 @ X3 @ (k1_tarski @ X4)) @ 
% 0.21/0.45            (k1_tarski @ X4)) = (X3))
% 0.21/0.45          | ~ (r2_hidden @ X4 @ X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [t140_zfmisc_1])).
% 0.21/0.45  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X3 : $i, X4 : $i]:
% 0.21/0.45         (((k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.21/0.45            (k4_xboole_0 @ X3 @ (k1_tarski @ X4))) = (X3))
% 0.21/0.45          | ~ (r2_hidden @ X4 @ X3))),
% 0.21/0.45      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (((k2_xboole_0 @ (k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) @ 
% 0.21/0.45         (k4_xboole_0 @ k1_xboole_0 @ 
% 0.21/0.45          (k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0))))
% 0.21/0.45         = (k1_xboole_0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.45  thf(t49_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X5 : $i, X6 : $i]:
% 0.21/0.45         ((k2_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.45  thf('12', plain, ($false),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
