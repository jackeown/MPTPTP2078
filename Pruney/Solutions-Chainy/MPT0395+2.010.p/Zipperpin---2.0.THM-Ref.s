%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xhPHnG9WEw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  162 ( 193 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t17_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_setfam_1 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t17_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
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
    ! [X11: $i,X12: $i] :
      ( ( r1_setfam_1 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_setfam_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r1_tarski @ ( sk_C @ X12 @ X11 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_B )
    | ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xhPHnG9WEw
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:59:45 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.45  % Solved by: fo/fo7.sh
% 0.23/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.45  % done 38 iterations in 0.013s
% 0.23/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.45  % SZS output start Refutation
% 0.23/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.45  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.23/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.45  thf(t17_setfam_1, conjecture,
% 0.23/0.45    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.23/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.45    (~( ![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ) )),
% 0.23/0.45    inference('cnf.neg', [status(esa)], [t17_setfam_1])).
% 0.23/0.45  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ sk_B)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(d2_setfam_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.23/0.45       ( ![C:$i]:
% 0.23/0.45         ( ~( ( r2_hidden @ C @ A ) & 
% 0.23/0.45              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.23/0.45  thf('2', plain,
% 0.23/0.45      (![X11 : $i, X12 : $i]:
% 0.23/0.45         ((r1_setfam_1 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 0.23/0.45      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.23/0.45  thf(l1_zfmisc_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.23/0.45  thf('3', plain,
% 0.23/0.45      (![X6 : $i, X8 : $i]:
% 0.23/0.45         ((r1_tarski @ (k1_tarski @ X6) @ X8) | ~ (r2_hidden @ X6 @ X8))),
% 0.23/0.45      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.23/0.45  thf('4', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         ((r1_setfam_1 @ X0 @ X1)
% 0.23/0.45          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.23/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.45  thf(t1_xboole_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i]:
% 0.23/0.45     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.23/0.45       ( r1_tarski @ A @ C ) ))).
% 0.23/0.45  thf('5', plain,
% 0.23/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.45         (~ (r1_tarski @ X3 @ X4)
% 0.23/0.45          | ~ (r1_tarski @ X4 @ X5)
% 0.23/0.45          | (r1_tarski @ X3 @ X5))),
% 0.23/0.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.23/0.45  thf('6', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.45         ((r1_setfam_1 @ X0 @ X1)
% 0.23/0.45          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X2)
% 0.23/0.45          | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.45  thf('7', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         ((r1_tarski @ (k1_tarski @ (sk_C @ X0 @ sk_A)) @ sk_B)
% 0.23/0.45          | (r1_setfam_1 @ sk_A @ X0))),
% 0.23/0.45      inference('sup-', [status(thm)], ['1', '6'])).
% 0.23/0.45  thf('8', plain,
% 0.23/0.45      (![X6 : $i, X7 : $i]:
% 0.23/0.45         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k1_tarski @ X6) @ X7))),
% 0.23/0.45      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.23/0.45  thf('9', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         ((r1_setfam_1 @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.23/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.45  thf(d10_xboole_0, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.45  thf('10', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.45  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.45      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.45  thf('12', plain,
% 0.23/0.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.45         ((r1_setfam_1 @ X11 @ X12)
% 0.23/0.45          | ~ (r2_hidden @ X13 @ X12)
% 0.23/0.45          | ~ (r1_tarski @ (sk_C @ X12 @ X11) @ X13))),
% 0.23/0.45      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.23/0.45  thf('13', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.23/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.45  thf('14', plain,
% 0.23/0.45      (((r1_setfam_1 @ sk_A @ sk_B) | (r1_setfam_1 @ sk_A @ sk_B))),
% 0.23/0.45      inference('sup-', [status(thm)], ['9', '13'])).
% 0.23/0.45  thf('15', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.23/0.45      inference('simplify', [status(thm)], ['14'])).
% 0.23/0.45  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.23/0.45  
% 0.23/0.45  % SZS output end Refutation
% 0.23/0.45  
% 0.23/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
