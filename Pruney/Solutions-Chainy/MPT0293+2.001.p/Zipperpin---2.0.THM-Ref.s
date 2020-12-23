%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C8hGyxmyYr

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:56 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  167 ( 185 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t100_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_zfmisc_1 @ ( k3_tarski @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X17 ) @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k1_tarski @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ ( k3_tarski @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X15 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_zfmisc_1 @ ( sk_C @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C8hGyxmyYr
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:56:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.44/1.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.44/1.62  % Solved by: fo/fo7.sh
% 1.44/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.62  % done 1509 iterations in 1.150s
% 1.44/1.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.44/1.62  % SZS output start Refutation
% 1.44/1.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.44/1.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.44/1.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.44/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.44/1.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.44/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.44/1.62  thf(t100_zfmisc_1, conjecture,
% 1.44/1.62    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 1.44/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.62    (~( ![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )),
% 1.44/1.62    inference('cnf.neg', [status(esa)], [t100_zfmisc_1])).
% 1.44/1.62  thf('0', plain, (~ (r1_tarski @ sk_A @ (k1_zfmisc_1 @ (k3_tarski @ sk_A)))),
% 1.44/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.62  thf(t80_zfmisc_1, axiom,
% 1.44/1.62    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.44/1.62  thf('1', plain,
% 1.44/1.62      (![X17 : $i]: (r1_tarski @ (k1_tarski @ X17) @ (k1_zfmisc_1 @ X17))),
% 1.44/1.62      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 1.44/1.62  thf(l1_zfmisc_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.44/1.62  thf('2', plain,
% 1.44/1.62      (![X10 : $i, X11 : $i]:
% 1.44/1.62         ((r2_hidden @ X10 @ X11) | ~ (r1_tarski @ (k1_tarski @ X10) @ X11))),
% 1.44/1.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.44/1.62  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.44/1.62      inference('sup-', [status(thm)], ['1', '2'])).
% 1.44/1.62  thf(d3_tarski, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( r1_tarski @ A @ B ) <=>
% 1.44/1.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.44/1.62  thf('4', plain,
% 1.44/1.62      (![X1 : $i, X3 : $i]:
% 1.44/1.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.44/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.62  thf(l49_zfmisc_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 1.44/1.62  thf('5', plain,
% 1.44/1.62      (![X13 : $i, X14 : $i]:
% 1.44/1.62         ((r1_tarski @ X13 @ (k3_tarski @ X14)) | ~ (r2_hidden @ X13 @ X14))),
% 1.44/1.62      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 1.44/1.62  thf('6', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i]:
% 1.44/1.62         ((r1_tarski @ X0 @ X1)
% 1.44/1.62          | (r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0)))),
% 1.44/1.62      inference('sup-', [status(thm)], ['4', '5'])).
% 1.44/1.62  thf(t79_zfmisc_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( r1_tarski @ A @ B ) =>
% 1.44/1.62       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.44/1.62  thf('7', plain,
% 1.44/1.62      (![X15 : $i, X16 : $i]:
% 1.44/1.62         ((r1_tarski @ (k1_zfmisc_1 @ X15) @ (k1_zfmisc_1 @ X16))
% 1.44/1.62          | ~ (r1_tarski @ X15 @ X16))),
% 1.44/1.62      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.44/1.62  thf('8', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i]:
% 1.44/1.62         ((r1_tarski @ X0 @ X1)
% 1.44/1.62          | (r1_tarski @ (k1_zfmisc_1 @ (sk_C @ X1 @ X0)) @ 
% 1.44/1.62             (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 1.44/1.62      inference('sup-', [status(thm)], ['6', '7'])).
% 1.44/1.62  thf('9', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.62         (~ (r2_hidden @ X0 @ X1)
% 1.44/1.62          | (r2_hidden @ X0 @ X2)
% 1.44/1.62          | ~ (r1_tarski @ X1 @ X2))),
% 1.44/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.62  thf('10', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.62         ((r1_tarski @ X0 @ X1)
% 1.44/1.62          | (r2_hidden @ X2 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 1.44/1.62          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ (sk_C @ X1 @ X0))))),
% 1.44/1.62      inference('sup-', [status(thm)], ['8', '9'])).
% 1.44/1.62  thf('11', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i]:
% 1.44/1.62         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 1.44/1.62          | (r1_tarski @ X0 @ X1))),
% 1.44/1.62      inference('sup-', [status(thm)], ['3', '10'])).
% 1.44/1.62  thf('12', plain,
% 1.44/1.62      (![X1 : $i, X3 : $i]:
% 1.44/1.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.44/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.62  thf('13', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         ((r1_tarski @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 1.44/1.62          | (r1_tarski @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 1.44/1.62      inference('sup-', [status(thm)], ['11', '12'])).
% 1.44/1.62  thf('14', plain,
% 1.44/1.62      (![X0 : $i]: (r1_tarski @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))),
% 1.44/1.62      inference('simplify', [status(thm)], ['13'])).
% 1.44/1.62  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 1.44/1.62  
% 1.44/1.62  % SZS output end Refutation
% 1.44/1.62  
% 1.44/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
