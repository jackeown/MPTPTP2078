%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7sBnYqoVeP

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  55 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  284 ( 452 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X11 ) )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t115_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ A )
        = ( k2_zfmisc_1 @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ A )
          = ( k2_zfmisc_1 @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t115_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_B ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['16','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7sBnYqoVeP
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:44:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 31 iterations in 0.033s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.46  thf(d3_tarski, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (![X1 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X1 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.46  thf(l54_zfmisc_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.46       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.22/0.46         ((r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X11))
% 0.22/0.46          | ~ (r2_hidden @ X9 @ X11)
% 0.22/0.46          | ~ (r2_hidden @ X7 @ X8))),
% 0.22/0.46      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X0 @ X1)
% 0.22/0.46          | ~ (r2_hidden @ X3 @ X2)
% 0.22/0.46          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.22/0.46             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X0 @ X1)
% 0.22/0.46          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.22/0.46             (k2_zfmisc_1 @ X0 @ X2))
% 0.22/0.46          | (r1_tarski @ X2 @ X3))),
% 0.22/0.46      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.46  thf(t115_zfmisc_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( k2_zfmisc_1 @ A @ A ) = ( k2_zfmisc_1 @ B @ B ) ) =>
% 0.22/0.46       ( ( A ) = ( B ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i]:
% 0.22/0.46        ( ( ( k2_zfmisc_1 @ A @ A ) = ( k2_zfmisc_1 @ B @ B ) ) =>
% 0.22/0.46          ( ( A ) = ( B ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t115_zfmisc_1])).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_zfmisc_1 @ sk_B @ sk_B))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.46         ((r2_hidden @ X7 @ X8)
% 0.22/0.46          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.22/0.46      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.22/0.46          | (r2_hidden @ X1 @ sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((r1_tarski @ sk_A @ X0)
% 0.22/0.46          | (r1_tarski @ sk_A @ X1)
% 0.22/0.46          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B) | (r1_tarski @ sk_A @ X0))),
% 0.22/0.46      inference('condensation', [status(thm)], ['8'])).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X1 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.46  thf('11', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.46  thf(d10_xboole_0, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.46  thf('13', plain,
% 0.22/0.46      (![X4 : $i, X6 : $i]:
% 0.22/0.46         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.46  thf('14', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf('15', plain, (((sk_A) != (sk_B))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('16', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.22/0.46      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('17', plain,
% 0.22/0.46      (((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_zfmisc_1 @ sk_B @ sk_B))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('18', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X0 @ X1)
% 0.22/0.46          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.22/0.46             (k2_zfmisc_1 @ X0 @ X2))
% 0.22/0.46          | (r1_tarski @ X2 @ X3))),
% 0.22/0.46      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.46  thf('19', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((r2_hidden @ (k4_tarski @ (sk_C @ X1 @ sk_B) @ (sk_C @ X0 @ sk_B)) @ 
% 0.22/0.46           (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.22/0.46          | (r1_tarski @ sk_B @ X0)
% 0.22/0.46          | (r1_tarski @ sk_B @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.46  thf('20', plain,
% 0.22/0.46      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.46         ((r2_hidden @ X7 @ X8)
% 0.22/0.46          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.22/0.46      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.46  thf('21', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((r1_tarski @ sk_B @ X1)
% 0.22/0.46          | (r1_tarski @ sk_B @ X0)
% 0.22/0.46          | (r2_hidden @ (sk_C @ X1 @ sk_B) @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.46  thf('22', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A) | (r1_tarski @ sk_B @ X0))),
% 0.22/0.46      inference('condensation', [status(thm)], ['21'])).
% 0.22/0.46  thf('23', plain,
% 0.22/0.46      (![X1 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.46  thf('24', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.46  thf('25', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.46      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.46  thf('26', plain, ($false), inference('demod', [status(thm)], ['16', '25'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
