%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jJT3PZKLgu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  223 ( 299 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t137_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) )
     => ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) )
       => ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t137_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X2 ) @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_B @ sk_D ) @ ( k3_xboole_0 @ sk_C @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X13 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('9',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jJT3PZKLgu
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 59 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(t137_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.49         ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) =>
% 0.21/0.49       ( r2_hidden @
% 0.21/0.49         A @ 
% 0.21/0.49         ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49        ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.49            ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) =>
% 0.21/0.49          ( r2_hidden @
% 0.21/0.49            A @ 
% 0.21/0.49            ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t137_zfmisc_1])).
% 0.21/0.49  thf('0', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l1_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X8 : $i, X10 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(l27_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k1_tarski @ X11) @ X12) | (r2_hidden @ X11 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.49  thf(t77_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.49          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X4 @ X5)
% 0.21/0.49          | ~ (r1_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.21/0.49          | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.49          | ~ (r1_tarski @ (k1_tarski @ X2) @ X0)
% 0.21/0.49          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.21/0.49          | (r2_hidden @ sk_A @ 
% 0.21/0.49             (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_D @ sk_E))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (~ (r2_hidden @ sk_A @ 
% 0.21/0.49          (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D) @ 
% 0.21/0.49           (k3_xboole_0 @ sk_C @ sk_E)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t123_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.21/0.49       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.49         ((k2_zfmisc_1 @ (k3_xboole_0 @ X13 @ X15) @ (k3_xboole_0 @ X14 @ X16))
% 0.21/0.49           = (k3_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 0.21/0.49              (k2_zfmisc_1 @ X15 @ X16)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (~ (r2_hidden @ sk_A @ 
% 0.21/0.49          (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.21/0.49           (k2_zfmisc_1 @ sk_D @ sk_E)))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('11', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf(t55_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k2_tarski @ X17 @ X18) @ X19)
% 0.21/0.49          | ~ (r2_hidden @ X17 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.49  thf('15', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain, ($false), inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
