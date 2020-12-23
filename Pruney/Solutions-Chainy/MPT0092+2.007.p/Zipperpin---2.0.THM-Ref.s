%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zEk6GQIXok

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  207 ( 295 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C_2 @ sk_B ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zEk6GQIXok
% 0.13/0.32  % Computer   : n018.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 14:21:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 41 iterations in 0.018s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.45  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.45  thf(t85_xboole_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.45        ( ( r1_tarski @ A @ B ) =>
% 0.19/0.45          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t85_xboole_1])).
% 0.19/0.45  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C_2 @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t3_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.45            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.45       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.45            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X10 : $i, X11 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.19/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X10 : $i, X11 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.19/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.45  thf(d5_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.45       ( ![D:$i]:
% 0.19/0.45         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.45           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X8 @ X7)
% 0.19/0.45          | ~ (r2_hidden @ X8 @ X6)
% 0.19/0.45          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.45      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X8 @ X6)
% 0.19/0.45          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.19/0.45          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['2', '4'])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.19/0.45          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['1', '5'])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.19/0.45      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      (![X10 : $i, X11 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.19/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.45  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(d3_tarski, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.45          | (r2_hidden @ X0 @ X2)
% 0.19/0.45          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['8', '11'])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X10 : $i, X11 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.19/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.45  thf('14', plain,
% 0.19/0.45      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X12 @ X10)
% 0.19/0.45          | ~ (r2_hidden @ X12 @ X13)
% 0.19/0.45          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.19/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.45  thf('15', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.45          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.45          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.19/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.45  thf('16', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ sk_A @ X0)
% 0.19/0.45          | ~ (r1_xboole_0 @ X0 @ sk_B)
% 0.19/0.45          | (r1_xboole_0 @ sk_A @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['12', '15'])).
% 0.19/0.45  thf('17', plain,
% 0.19/0.45      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ sk_A @ X0))),
% 0.19/0.45      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.45  thf('18', plain,
% 0.19/0.45      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['7', '17'])).
% 0.19/0.45  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
