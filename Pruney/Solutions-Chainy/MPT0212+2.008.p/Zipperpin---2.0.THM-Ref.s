%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9525nnFw5M

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  56 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  229 ( 404 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22
        = ( k1_zfmisc_1 @ X19 ) )
      | ( r1_tarski @ ( sk_C_1 @ X22 @ X19 ) @ X19 )
      | ( r2_hidden @ ( sk_C_1 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t1_zfmisc_1,conjecture,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t1_zfmisc_1])).

thf('8',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22
        = ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ ( sk_C_1 @ X22 @ X19 ) @ X19 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16','17','19'])).

thf('21',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9525nnFw5M
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:10:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 38 iterations in 0.032s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(d1_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X19 : $i, X22 : $i]:
% 0.19/0.47         (((X22) = (k1_zfmisc_1 @ X19))
% 0.19/0.47          | (r1_tarski @ (sk_C_1 @ X22 @ X19) @ X19)
% 0.19/0.47          | (r2_hidden @ (sk_C_1 @ X22 @ X19) @ X22))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.47  thf(t3_xboole_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.47          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.47          | ((sk_C_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf(d1_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X3 : $i, X6 : $i]:
% 0.19/0.47         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.47          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.47          | ((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (X0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((X0) != (k1_xboole_0))
% 0.19/0.47          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.47          | ((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.47      inference('eq_fact', [status(thm)], ['5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      ((((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.47        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.47  thf(t1_zfmisc_1, conjecture,
% 0.19/0.47    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.19/0.47  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X19 : $i, X22 : $i]:
% 0.19/0.47         (((X22) = (k1_zfmisc_1 @ X19))
% 0.19/0.47          | ~ (r1_tarski @ (sk_C_1 @ X22 @ X19) @ X19)
% 0.19/0.47          | ~ (r2_hidden @ (sk_C_1 @ X22 @ X19) @ X22))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.19/0.47        | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.19/0.47             (k1_tarski @ k1_xboole_0))
% 0.19/0.47        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf(t17_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.47      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.47      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.47  thf('16', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.47  thf('19', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.19/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.47  thf('20', plain, (((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['11', '16', '17', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('22', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
