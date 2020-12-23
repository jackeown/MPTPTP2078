%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GsW18QNSBb

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :  118 ( 140 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
      | ( X12 = X13 ) ) ),
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

thf('3',plain,
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

thf('4',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    $false ),
    inference('sup-',[status(thm)],['1','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GsW18QNSBb
% 0.15/0.37  % Computer   : n012.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:49:07 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.24/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.44  % Solved by: fo/fo7.sh
% 0.24/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.44  % done 20 iterations in 0.008s
% 0.24/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.44  % SZS output start Refutation
% 0.24/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.44  thf(d1_tarski, axiom,
% 0.24/0.44    (![A:$i,B:$i]:
% 0.24/0.44     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.24/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.24/0.44  thf('0', plain,
% 0.24/0.44      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.44         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.24/0.44      inference('cnf', [status(esa)], [d1_tarski])).
% 0.24/0.44  thf('1', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.24/0.44      inference('simplify', [status(thm)], ['0'])).
% 0.24/0.44  thf(t17_zfmisc_1, axiom,
% 0.24/0.44    (![A:$i,B:$i]:
% 0.24/0.44     ( ( ( A ) != ( B ) ) =>
% 0.24/0.44       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.24/0.44  thf('2', plain,
% 0.24/0.44      (![X12 : $i, X13 : $i]:
% 0.24/0.44         ((r1_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13))
% 0.24/0.44          | ((X12) = (X13)))),
% 0.24/0.44      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.24/0.44  thf(t18_zfmisc_1, conjecture,
% 0.24/0.44    (![A:$i,B:$i]:
% 0.24/0.44     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.24/0.44         ( k1_tarski @ A ) ) =>
% 0.24/0.44       ( ( A ) = ( B ) ) ))).
% 0.24/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.44    (~( ![A:$i,B:$i]:
% 0.24/0.44        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.24/0.44            ( k1_tarski @ A ) ) =>
% 0.24/0.44          ( ( A ) = ( B ) ) ) )),
% 0.24/0.44    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.24/0.44  thf('3', plain,
% 0.24/0.44      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.44         = (k1_tarski @ sk_A))),
% 0.24/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.44  thf(t4_xboole_0, axiom,
% 0.24/0.44    (![A:$i,B:$i]:
% 0.24/0.44     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.44            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.44  thf('4', plain,
% 0.24/0.44      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.24/0.44         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.24/0.44          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.24/0.44      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.44  thf('5', plain,
% 0.24/0.44      (![X0 : $i]:
% 0.24/0.44         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.24/0.44          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.24/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.44  thf('6', plain,
% 0.24/0.44      (![X0 : $i]:
% 0.24/0.44         (((sk_A) = (sk_B)) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.44      inference('sup-', [status(thm)], ['2', '5'])).
% 0.24/0.44  thf('7', plain, (((sk_A) != (sk_B))),
% 0.24/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.44  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.24/0.44      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.24/0.44  thf('9', plain, ($false), inference('sup-', [status(thm)], ['1', '8'])).
% 0.24/0.44  
% 0.24/0.44  % SZS output end Refutation
% 0.24/0.44  
% 0.24/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
