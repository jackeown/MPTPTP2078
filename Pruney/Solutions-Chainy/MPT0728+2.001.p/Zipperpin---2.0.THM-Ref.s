%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YmpUGXo1jb

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  71 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  264 ( 436 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t10_ordinal1,conjecture,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t10_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( k1_ordinal1 @ X20 )
      = ( k2_xboole_0 @ X20 @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t141_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ ( k1_tarski @ X13 ) ) @ ( k1_tarski @ X13 ) )
        = X12 )
      | ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t141_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ ( k1_tarski @ X19 ) )
        = X18 )
      | ( r2_hidden @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X0 @ X0 )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X20: $i] :
      ( ( k1_ordinal1 @ X20 )
      = ( k2_xboole_0 @ X20 @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ( X0
        = ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('12',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( sk_A
    = ( k1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,
    ( sk_A
    = ( k1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X20: $i] :
      ( ( k1_ordinal1 @ X20 )
      = ( k2_xboole_0 @ X20 @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t47_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ X14 @ X16 ) @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 )
      | ( r2_hidden @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['14','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YmpUGXo1jb
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 58 iterations in 0.031s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(t10_ordinal1, conjecture,
% 0.22/0.49    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 0.22/0.49  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d1_ordinal1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X20 : $i]:
% 0.22/0.49         ((k1_ordinal1 @ X20) = (k2_xboole_0 @ X20 @ (k1_tarski @ X20)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.22/0.49  thf(t141_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( r2_hidden @ A @ B ) ) =>
% 0.22/0.49       ( ( k4_xboole_0 @
% 0.22/0.49           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.22/0.49         ( B ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ (k2_xboole_0 @ X12 @ (k1_tarski @ X13)) @ 
% 0.22/0.49            (k1_tarski @ X13)) = (X12))
% 0.22/0.49          | (r2_hidden @ X13 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t141_zfmisc_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.22/0.49          | (r2_hidden @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf(t65_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.49       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X18 @ (k1_tarski @ X19)) = (X18))
% 0.22/0.49          | (r2_hidden @ X19 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((X0) = (k1_ordinal1 @ X0))
% 0.22/0.49          | (r2_hidden @ X0 @ X0)
% 0.22/0.49          | (r2_hidden @ X0 @ (k1_ordinal1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X20 : $i]:
% 0.22/0.49         ((k1_ordinal1 @ X20) = (k2_xboole_0 @ X20 @ (k1_tarski @ X20)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.22/0.49  thf(t7_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.49  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf(d3_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ X3)
% 0.22/0.49          | (r2_hidden @ X2 @ X4)
% 0.22/0.49          | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ X0 @ (k1_ordinal1 @ X0)) | ((X0) = (k1_ordinal1 @ X0)))),
% 0.22/0.49      inference('clc', [status(thm)], ['5', '10'])).
% 0.22/0.49  thf('12', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain, (((sk_A) = (k1_ordinal1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '13'])).
% 0.22/0.49  thf('15', plain, (((sk_A) = (k1_ordinal1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X20 : $i]:
% 0.22/0.49         ((k1_ordinal1 @ X20) = (k2_xboole_0 @ X20 @ (k1_tarski @ X20)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.22/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t47_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.22/0.49       ( r2_hidden @ A @ C ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         ((r2_hidden @ X14 @ X15)
% 0.22/0.49          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_tarski @ X14 @ X16) @ X15) @ X15))),
% 0.22/0.49      inference('cnf', [status(esa)], [t47_zfmisc_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ X1)
% 0.22/0.49          | (r2_hidden @ X0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1)
% 0.22/0.49          | (r2_hidden @ X0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0) | (r2_hidden @ X0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '21'])).
% 0.22/0.49  thf('23', plain, ((~ (r1_tarski @ sk_A @ sk_A) | (r2_hidden @ sk_A @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '22'])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('25', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.22/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.49  thf('26', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['23', '25'])).
% 0.22/0.49  thf('27', plain, ($false), inference('demod', [status(thm)], ['14', '26'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
