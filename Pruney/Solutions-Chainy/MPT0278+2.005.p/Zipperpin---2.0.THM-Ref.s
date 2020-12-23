%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CnCuz5Im3Z

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:42 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  355 ( 559 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t79_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_tarski @ X18 @ X16 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C @ X2 @ ( k1_zfmisc_1 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CnCuz5Im3Z
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.80/2.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.80/2.01  % Solved by: fo/fo7.sh
% 1.80/2.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/2.01  % done 2435 iterations in 1.554s
% 1.80/2.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.80/2.01  % SZS output start Refutation
% 1.80/2.01  thf(sk_B_type, type, sk_B: $i).
% 1.80/2.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/2.01  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.80/2.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.80/2.01  thf(sk_A_type, type, sk_A: $i).
% 1.80/2.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.80/2.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.80/2.01  thf(t79_zfmisc_1, conjecture,
% 1.80/2.01    (![A:$i,B:$i]:
% 1.80/2.01     ( ( r1_tarski @ A @ B ) =>
% 1.80/2.01       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.80/2.01  thf(zf_stmt_0, negated_conjecture,
% 1.80/2.01    (~( ![A:$i,B:$i]:
% 1.80/2.01        ( ( r1_tarski @ A @ B ) =>
% 1.80/2.01          ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 1.80/2.01    inference('cnf.neg', [status(esa)], [t79_zfmisc_1])).
% 1.80/2.01  thf('0', plain,
% 1.80/2.01      (~ (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 1.80/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.01  thf(d10_xboole_0, axiom,
% 1.80/2.01    (![A:$i,B:$i]:
% 1.80/2.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.80/2.01  thf('1', plain,
% 1.80/2.01      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.80/2.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.80/2.01  thf('2', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.80/2.01      inference('simplify', [status(thm)], ['1'])).
% 1.80/2.01  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.80/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.01  thf(t8_xboole_1, axiom,
% 1.80/2.01    (![A:$i,B:$i,C:$i]:
% 1.80/2.01     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.80/2.01       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.80/2.01  thf('4', plain,
% 1.80/2.01      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.80/2.01         (~ (r1_tarski @ X12 @ X13)
% 1.80/2.01          | ~ (r1_tarski @ X14 @ X13)
% 1.80/2.01          | (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ X13))),
% 1.80/2.01      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.80/2.01  thf('5', plain,
% 1.80/2.01      (![X0 : $i]:
% 1.80/2.01         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 1.80/2.01          | ~ (r1_tarski @ X0 @ sk_B))),
% 1.80/2.01      inference('sup-', [status(thm)], ['3', '4'])).
% 1.80/2.01  thf('6', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 1.80/2.01      inference('sup-', [status(thm)], ['2', '5'])).
% 1.80/2.01  thf('7', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.80/2.01      inference('simplify', [status(thm)], ['1'])).
% 1.80/2.01  thf(t10_xboole_1, axiom,
% 1.80/2.01    (![A:$i,B:$i,C:$i]:
% 1.80/2.01     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.80/2.01  thf('8', plain,
% 1.80/2.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.80/2.01         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ X7 @ (k2_xboole_0 @ X9 @ X8)))),
% 1.80/2.01      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.80/2.01  thf('9', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.80/2.01      inference('sup-', [status(thm)], ['7', '8'])).
% 1.80/2.01  thf('10', plain,
% 1.80/2.01      (![X4 : $i, X6 : $i]:
% 1.80/2.01         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.80/2.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.80/2.01  thf('11', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i]:
% 1.80/2.01         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.80/2.01          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 1.80/2.01      inference('sup-', [status(thm)], ['9', '10'])).
% 1.80/2.01  thf('12', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.80/2.01      inference('sup-', [status(thm)], ['6', '11'])).
% 1.80/2.01  thf(t7_xboole_1, axiom,
% 1.80/2.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.80/2.01  thf('13', plain,
% 1.80/2.01      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 1.80/2.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.80/2.01  thf('14', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.80/2.01      inference('sup-', [status(thm)], ['7', '8'])).
% 1.80/2.01  thf('15', plain,
% 1.80/2.01      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.80/2.01         (~ (r1_tarski @ X12 @ X13)
% 1.80/2.01          | ~ (r1_tarski @ X14 @ X13)
% 1.80/2.01          | (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ X13))),
% 1.80/2.01      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.80/2.01  thf('16', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.01         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 1.80/2.01          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.80/2.01      inference('sup-', [status(thm)], ['14', '15'])).
% 1.80/2.01  thf('17', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i]:
% 1.80/2.01         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 1.80/2.01      inference('sup-', [status(thm)], ['13', '16'])).
% 1.80/2.01  thf('18', plain,
% 1.80/2.01      (![X4 : $i, X6 : $i]:
% 1.80/2.01         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.80/2.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.80/2.01  thf('19', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i]:
% 1.80/2.01         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 1.80/2.01          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 1.80/2.01      inference('sup-', [status(thm)], ['17', '18'])).
% 1.80/2.01  thf('20', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i]:
% 1.80/2.01         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 1.80/2.01      inference('sup-', [status(thm)], ['13', '16'])).
% 1.80/2.01  thf('21', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.80/2.01      inference('demod', [status(thm)], ['19', '20'])).
% 1.80/2.01  thf(d3_tarski, axiom,
% 1.80/2.01    (![A:$i,B:$i]:
% 1.80/2.01     ( ( r1_tarski @ A @ B ) <=>
% 1.80/2.01       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.80/2.01  thf('22', plain,
% 1.80/2.01      (![X1 : $i, X3 : $i]:
% 1.80/2.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.80/2.01      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/2.01  thf(d1_zfmisc_1, axiom,
% 1.80/2.01    (![A:$i,B:$i]:
% 1.80/2.01     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.80/2.01       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.80/2.01  thf('23', plain,
% 1.80/2.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.80/2.01         (~ (r2_hidden @ X18 @ X17)
% 1.80/2.01          | (r1_tarski @ X18 @ X16)
% 1.80/2.01          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 1.80/2.01      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.80/2.01  thf('24', plain,
% 1.80/2.01      (![X16 : $i, X18 : $i]:
% 1.80/2.01         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 1.80/2.01      inference('simplify', [status(thm)], ['23'])).
% 1.80/2.01  thf('25', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i]:
% 1.80/2.01         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 1.80/2.01          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 1.80/2.01      inference('sup-', [status(thm)], ['22', '24'])).
% 1.80/2.01  thf('26', plain,
% 1.80/2.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.80/2.01         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ X7 @ (k2_xboole_0 @ X9 @ X8)))),
% 1.80/2.01      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.80/2.01  thf('27', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.01         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 1.80/2.01          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ 
% 1.80/2.01             (k2_xboole_0 @ X2 @ X0)))),
% 1.80/2.01      inference('sup-', [status(thm)], ['25', '26'])).
% 1.80/2.01  thf('28', plain,
% 1.80/2.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.01         ((r1_tarski @ (sk_C @ X2 @ (k1_zfmisc_1 @ X1)) @ 
% 1.80/2.01           (k2_xboole_0 @ X1 @ X0))
% 1.80/2.01          | (r1_tarski @ (k1_zfmisc_1 @ X1) @ X2))),
% 1.80/2.01      inference('sup+', [status(thm)], ['21', '27'])).
% 1.80/2.01  thf('29', plain,
% 1.80/2.01      (![X0 : $i]:
% 1.80/2.01         ((r1_tarski @ (sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 1.80/2.01          | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ X0))),
% 1.80/2.01      inference('sup+', [status(thm)], ['12', '28'])).
% 1.80/2.01  thf('30', plain,
% 1.80/2.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.80/2.01         (~ (r1_tarski @ X15 @ X16)
% 1.80/2.01          | (r2_hidden @ X15 @ X17)
% 1.80/2.01          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 1.80/2.01      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.80/2.01  thf('31', plain,
% 1.80/2.01      (![X15 : $i, X16 : $i]:
% 1.80/2.01         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 1.80/2.01      inference('simplify', [status(thm)], ['30'])).
% 1.80/2.01  thf('32', plain,
% 1.80/2.01      (![X0 : $i]:
% 1.80/2.01         ((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ X0)
% 1.80/2.01          | (r2_hidden @ (sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 1.80/2.01             (k1_zfmisc_1 @ sk_B)))),
% 1.80/2.01      inference('sup-', [status(thm)], ['29', '31'])).
% 1.80/2.01  thf('33', plain,
% 1.80/2.01      (![X1 : $i, X3 : $i]:
% 1.80/2.01         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.80/2.01      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/2.01  thf('34', plain,
% 1.80/2.01      (((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 1.80/2.01        | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)))),
% 1.80/2.01      inference('sup-', [status(thm)], ['32', '33'])).
% 1.80/2.01  thf('35', plain, ((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 1.80/2.01      inference('simplify', [status(thm)], ['34'])).
% 1.80/2.01  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 1.80/2.01  
% 1.80/2.01  % SZS output end Refutation
% 1.80/2.01  
% 1.80/2.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
