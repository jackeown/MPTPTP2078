%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1R2jtn3wt6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  199 ( 232 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t95_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X10 ) @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X2 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k1_tarski @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ ( k3_tarski @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X10 ) @ X11 )
      | ~ ( r1_tarski @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['0','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1R2jtn3wt6
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 22 iterations in 0.016s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(t95_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( r1_tarski @ A @ B ) =>
% 0.20/0.46          ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t95_zfmisc_1])).
% 0.20/0.46  thf('0', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t94_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.20/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X10) @ X11)
% 0.20/0.46          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.46  thf(l1_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X5 : $i, X7 : $i]:
% 0.20/0.46         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.20/0.46          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t12_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.20/0.46          | ((k2_xboole_0 @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0) = (X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(t11_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.46          | (r1_tarski @ (k3_tarski @ X0) @ X2)
% 0.20/0.46          | (r1_tarski @ (k1_tarski @ (sk_C @ X2 @ X0)) @ X1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ (k1_tarski @ (sk_C @ X0 @ sk_A)) @ sk_B)
% 0.20/0.46          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]:
% 0.20/0.46         ((r2_hidden @ X5 @ X6) | ~ (r1_tarski @ (k1_tarski @ X5) @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.20/0.46          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf(l49_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         ((r1_tarski @ X8 @ (k3_tarski @ X9)) | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.20/0.46          | (r1_tarski @ (sk_C @ X0 @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X10) @ X11)
% 0.20/0.46          | ~ (r1_tarski @ (sk_C @ X11 @ X10) @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))
% 0.20/0.46        | (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.20/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.46  thf('17', plain, ($false), inference('demod', [status(thm)], ['0', '16'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
