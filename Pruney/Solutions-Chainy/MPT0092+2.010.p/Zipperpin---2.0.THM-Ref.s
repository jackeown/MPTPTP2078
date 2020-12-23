%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vaIhmXrnTk

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:45 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  204 ( 292 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t85_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vaIhmXrnTk
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 17:15:45 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running portfolio for 600 s
% 0.11/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.31  % Number of cores: 8
% 0.11/0.31  % Python version: Python 3.6.8
% 0.18/0.32  % Running in FO mode
% 0.18/0.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.41  % Solved by: fo/fo7.sh
% 0.18/0.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.41  % done 23 iterations in 0.012s
% 0.18/0.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.41  % SZS output start Refutation
% 0.18/0.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.41  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.41  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.41  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.18/0.41  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.18/0.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.41  thf(t85_xboole_1, conjecture,
% 0.18/0.41    (![A:$i,B:$i,C:$i]:
% 0.18/0.41     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.18/0.41  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.41    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.41        ( ( r1_tarski @ A @ B ) =>
% 0.18/0.41          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )),
% 0.18/0.41    inference('cnf.neg', [status(esa)], [t85_xboole_1])).
% 0.18/0.41  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 0.18/0.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.41  thf(t3_xboole_0, axiom,
% 0.18/0.41    (![A:$i,B:$i]:
% 0.18/0.41     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.18/0.41            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.18/0.41       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.18/0.41            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.18/0.41  thf('1', plain,
% 0.18/0.41      (![X6 : $i, X7 : $i]:
% 0.18/0.41         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.18/0.41      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.18/0.41  thf('2', plain,
% 0.18/0.41      (![X6 : $i, X7 : $i]:
% 0.18/0.41         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.18/0.41      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.18/0.41  thf(d5_xboole_0, axiom,
% 0.18/0.41    (![A:$i,B:$i,C:$i]:
% 0.18/0.41     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.18/0.41       ( ![D:$i]:
% 0.18/0.41         ( ( r2_hidden @ D @ C ) <=>
% 0.18/0.41           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.18/0.41  thf('3', plain,
% 0.18/0.41      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.18/0.41         (~ (r2_hidden @ X4 @ X3)
% 0.18/0.41          | ~ (r2_hidden @ X4 @ X2)
% 0.18/0.41          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.41      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.18/0.41  thf('4', plain,
% 0.18/0.41      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.18/0.41         (~ (r2_hidden @ X4 @ X2)
% 0.18/0.41          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.41      inference('simplify', [status(thm)], ['3'])).
% 0.18/0.41  thf('5', plain,
% 0.18/0.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.41         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.18/0.41          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.18/0.41      inference('sup-', [status(thm)], ['2', '4'])).
% 0.18/0.41  thf('6', plain,
% 0.18/0.41      (![X0 : $i, X1 : $i]:
% 0.18/0.41         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.18/0.41          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.18/0.41      inference('sup-', [status(thm)], ['1', '5'])).
% 0.18/0.41  thf('7', plain,
% 0.18/0.41      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.18/0.41      inference('simplify', [status(thm)], ['6'])).
% 0.18/0.41  thf('8', plain,
% 0.18/0.41      (![X6 : $i, X7 : $i]:
% 0.18/0.41         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.18/0.41      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.18/0.41  thf('9', plain,
% 0.18/0.41      (![X6 : $i, X7 : $i]:
% 0.18/0.41         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.18/0.41      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.18/0.41  thf('10', plain,
% 0.18/0.41      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.18/0.41         (~ (r2_hidden @ X8 @ X6)
% 0.18/0.41          | ~ (r2_hidden @ X8 @ X9)
% 0.18/0.41          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.18/0.41      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.18/0.41  thf('11', plain,
% 0.18/0.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.41         ((r1_xboole_0 @ X1 @ X0)
% 0.18/0.41          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.18/0.41          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.18/0.41      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.41  thf('12', plain,
% 0.18/0.41      (![X0 : $i, X1 : $i]:
% 0.18/0.41         ((r1_xboole_0 @ X0 @ X1)
% 0.18/0.41          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.18/0.41          | (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.41      inference('sup-', [status(thm)], ['8', '11'])).
% 0.18/0.41  thf('13', plain,
% 0.18/0.41      (![X0 : $i, X1 : $i]:
% 0.18/0.41         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.41      inference('simplify', [status(thm)], ['12'])).
% 0.18/0.41  thf('14', plain,
% 0.18/0.41      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.18/0.41      inference('sup-', [status(thm)], ['7', '13'])).
% 0.18/0.41  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.41  thf(t63_xboole_1, axiom,
% 0.18/0.41    (![A:$i,B:$i,C:$i]:
% 0.18/0.41     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.18/0.41       ( r1_xboole_0 @ A @ C ) ))).
% 0.18/0.41  thf('16', plain,
% 0.18/0.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.41         (~ (r1_tarski @ X10 @ X11)
% 0.18/0.41          | ~ (r1_xboole_0 @ X11 @ X12)
% 0.18/0.41          | (r1_xboole_0 @ X10 @ X12))),
% 0.18/0.41      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.18/0.41  thf('17', plain,
% 0.18/0.41      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.18/0.41      inference('sup-', [status(thm)], ['15', '16'])).
% 0.18/0.41  thf('18', plain,
% 0.18/0.41      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.18/0.41      inference('sup-', [status(thm)], ['14', '17'])).
% 0.18/0.41  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.18/0.41  
% 0.18/0.41  % SZS output end Refutation
% 0.18/0.41  
% 0.18/0.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
