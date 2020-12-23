%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4W78wWtQxH

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 ( 250 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t75_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t75_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4W78wWtQxH
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 133 iterations in 0.141s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.59  thf(t75_xboole_1, conjecture,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.59          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i,B:$i]:
% 0.21/0.59        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.59             ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t75_xboole_1])).
% 0.21/0.59  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('1', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t4_xboole_0, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.59  thf('2', plain,
% 0.21/0.59      (![X12 : $i, X13 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ X12 @ X13)
% 0.21/0.59          | (r2_hidden @ (sk_C @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (![X12 : $i, X13 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ X12 @ X13)
% 0.21/0.59          | (r2_hidden @ (sk_C @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.59  thf(d4_xboole_0, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.59       ( ![D:$i]:
% 0.21/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.59           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.59  thf('4', plain,
% 0.21/0.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.59          | (r2_hidden @ X10 @ X8)
% 0.21/0.59          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.59         ((r2_hidden @ X10 @ X8)
% 0.21/0.59          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.59          | ~ (r2_hidden @ X6 @ X8)
% 0.21/0.59          | (r2_hidden @ X6 @ X9)
% 0.21/0.59          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.59         ((r2_hidden @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 0.21/0.59          | ~ (r2_hidden @ X6 @ X8)
% 0.21/0.59          | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.59      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.59          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 0.21/0.59          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.59          | (r2_hidden @ (sk_C @ X0 @ X1) @ 
% 0.21/0.59             (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.21/0.59          | (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((r2_hidden @ (sk_C @ X0 @ X1) @ 
% 0.21/0.59           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.21/0.59          | (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.21/0.59          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.21/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.59          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.59  thf('14', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.59      inference('sup-', [status(thm)], ['1', '13'])).
% 0.21/0.59  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
