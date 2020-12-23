%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AxhvHQnxUI

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:59 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  195 ( 249 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AxhvHQnxUI
% 0.17/0.37  % Computer   : n021.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 17:44:35 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 27 iterations in 0.018s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.50  thf(t45_zfmisc_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.24/0.50       ( r2_hidden @ A @ B ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i]:
% 0.24/0.50        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.24/0.50          ( r2_hidden @ A @ B ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.24/0.50  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t69_enumset1, axiom,
% 0.24/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.50  thf('1', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.24/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.50  thf(d2_tarski, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.24/0.50       ( ![D:$i]:
% 0.24/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.50         (((X7) != (X6))
% 0.24/0.50          | (r2_hidden @ X7 @ X8)
% 0.24/0.50          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.24/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.24/0.50  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['1', '3'])).
% 0.24/0.50  thf(d3_tarski, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X1 : $i, X3 : $i]:
% 0.24/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.50  thf(t7_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.24/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.50          | (r2_hidden @ X0 @ X2)
% 0.24/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.50         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.24/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.50         ((r1_tarski @ X0 @ X1)
% 0.24/0.50          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['5', '8'])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.50          | (r2_hidden @ X0 @ X2)
% 0.24/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r2_hidden @ X0 @ sk_B)
% 0.24/0.50          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.24/0.50          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.24/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      (![X1 : $i, X3 : $i]:
% 0.24/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.50  thf('15', plain,
% 0.24/0.50      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 0.24/0.50        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 0.24/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.50  thf('16', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.24/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.50          | (r2_hidden @ X0 @ X2)
% 0.24/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.50  thf('19', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.24/0.50      inference('sup-', [status(thm)], ['4', '18'])).
% 0.24/0.50  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
