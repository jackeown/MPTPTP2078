%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gwG2lmbJrG

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  140 ( 162 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) )
      | ( X15 = X16 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gwG2lmbJrG
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:41:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 26 iterations in 0.020s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(t69_enumset1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.46  thf('0', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.19/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.46  thf(d2_tarski, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.46       ( ![D:$i]:
% 0.19/0.46         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.46         (((X7) != (X6))
% 0.19/0.46          | (r2_hidden @ X7 @ X8)
% 0.19/0.46          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.19/0.46      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.46  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['0', '2'])).
% 0.19/0.46  thf(t17_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( A ) != ( B ) ) =>
% 0.19/0.46       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X15 : $i, X16 : $i]:
% 0.19/0.46         ((r1_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16))
% 0.19/0.46          | ((X15) = (X16)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.19/0.46  thf(t18_zfmisc_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.46         ( k1_tarski @ A ) ) =>
% 0.19/0.46       ( ( A ) = ( B ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.46            ( k1_tarski @ A ) ) =>
% 0.19/0.46          ( ( A ) = ( B ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46         = (k1_tarski @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t4_xboole_0, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.46            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.19/0.46          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.19/0.46          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((sk_A) = (sk_B)) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.46  thf('9', plain, (((sk_A) != (sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf('11', plain, ($false), inference('sup-', [status(thm)], ['3', '10'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
