%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4x3NobvTdf

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  111 ( 131 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X12 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X9: $i,X12: $i] :
      ( r2_hidden @ X12 @ ( k2_tarski @ X12 @ X9 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    $false ),
    inference(demod,[status(thm)],['0','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4x3NobvTdf
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.21/0.34  % Running in FO mode
% 0.21/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.43  % Solved by: fo/fo7.sh
% 0.21/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.43  % done 26 iterations in 0.017s
% 0.21/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.43  % SZS output start Refutation
% 0.21/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.43  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.43  thf(t47_zfmisc_1, conjecture,
% 0.21/0.43    (![A:$i,B:$i,C:$i]:
% 0.21/0.43     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.43       ( r2_hidden @ A @ C ) ))).
% 0.21/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.43    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.43        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.43          ( r2_hidden @ A @ C ) ) )),
% 0.21/0.43    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.21/0.43  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf(d2_tarski, axiom,
% 0.21/0.43    (![A:$i,B:$i,C:$i]:
% 0.21/0.43     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.43       ( ![D:$i]:
% 0.21/0.43         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.43  thf('1', plain,
% 0.21/0.43      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.43         (((X10) != (X12))
% 0.21/0.43          | (r2_hidden @ X10 @ X11)
% 0.21/0.43          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 0.21/0.43      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.43  thf('2', plain,
% 0.21/0.43      (![X9 : $i, X12 : $i]: (r2_hidden @ X12 @ (k2_tarski @ X12 @ X9))),
% 0.21/0.43      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.43  thf('3', plain,
% 0.21/0.43      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf(t11_xboole_1, axiom,
% 0.21/0.43    (![A:$i,B:$i,C:$i]:
% 0.21/0.43     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.21/0.43  thf('4', plain,
% 0.21/0.43      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.43         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.21/0.43      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.43  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.21/0.43      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.43  thf(d3_tarski, axiom,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.43       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.43  thf('6', plain,
% 0.21/0.43      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.43         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.43          | (r2_hidden @ X2 @ X4)
% 0.21/0.43          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.43  thf('7', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         ((r2_hidden @ X0 @ sk_C_1)
% 0.21/0.43          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.43      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.43  thf('8', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.21/0.43      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.43  thf('9', plain, ($false), inference('demod', [status(thm)], ['0', '8'])).
% 0.21/0.43  
% 0.21/0.43  % SZS output end Refutation
% 0.21/0.43  
% 0.21/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
