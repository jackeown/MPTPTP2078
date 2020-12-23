%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.57m0B7pdna

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  212 ( 256 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X13 != X12 )
      | ( r2_hidden @ X13 @ X14 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_tarski @ X12 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.57m0B7pdna
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:27:34 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.33  % Running portfolio for 600 s
% 0.19/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 107 iterations in 0.051s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(t21_zfmisc_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.50         ( k1_xboole_0 ) ) =>
% 0.19/0.50       ( ( A ) = ( B ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.50            ( k1_xboole_0 ) ) =>
% 0.19/0.50          ( ( A ) = ( B ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d1_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.50         (((X13) != (X12))
% 0.19/0.50          | (r2_hidden @ X13 @ X14)
% 0.19/0.50          | ((X14) != (k1_tarski @ X12)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.50  thf('2', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_tarski @ X12))),
% 0.19/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.50  thf(d5_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.50       ( ![D:$i]:
% 0.19/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | (r2_hidden @ X0 @ X3)
% 0.19/0.50          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.19/0.50        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['0', '5'])).
% 0.19/0.50  thf(t2_boole, axiom,
% 0.19/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.50  thf(t100_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]:
% 0.19/0.50         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.50           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf(t5_boole, axiom,
% 0.19/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.50  thf('10', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.50  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.50          | ~ (r2_hidden @ X4 @ X2)
% 0.19/0.50          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.50          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '13'])).
% 0.19/0.50  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.50      inference('condensation', [status(thm)], ['14'])).
% 0.19/0.50  thf('16', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.19/0.50      inference('clc', [status(thm)], ['6', '15'])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X15 @ X14)
% 0.19/0.50          | ((X15) = (X12))
% 0.19/0.50          | ((X14) != (k1_tarski @ X12)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X12 : $i, X15 : $i]:
% 0.19/0.50         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.50  thf('19', plain, (((sk_A) = (sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '18'])).
% 0.19/0.50  thf('20', plain, (((sk_A) != (sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('21', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
