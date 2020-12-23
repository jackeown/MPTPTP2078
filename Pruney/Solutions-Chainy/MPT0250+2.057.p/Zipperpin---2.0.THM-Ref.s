%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qtrtns9FB4

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 157 expanded)
%              Number of leaves         :   14 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  287 (1160 expanded)
%              Number of equality atoms :   17 (  60 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( sk_B_1
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X55 @ X54 )
      | ~ ( r1_tarski @ ( k2_tarski @ X53 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('9',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X53 @ X54 )
      | ~ ( r1_tarski @ ( k2_tarski @ X53 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X53: $i,X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X53 @ X55 ) @ X56 )
      | ~ ( r2_hidden @ X55 @ X56 )
      | ~ ( r2_hidden @ X53 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('24',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['24','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X53 @ X54 )
      | ~ ( r1_tarski @ ( k2_tarski @ X53 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qtrtns9FB4
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:12:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 304 iterations in 0.103s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(t45_zfmisc_1, conjecture,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.19/0.55       ( r2_hidden @ A @ B ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i]:
% 0.19/0.55        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.19/0.55          ( r2_hidden @ A @ B ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.19/0.55  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ sk_B_1)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d10_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X10 : $i, X12 : $i]:
% 0.19/0.55         (((X10) = (X12))
% 0.19/0.55          | ~ (r1_tarski @ X12 @ X10)
% 0.19/0.55          | ~ (r1_tarski @ X10 @ X12))),
% 0.19/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.19/0.55        | ((sk_B_1) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.55  thf('5', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.19/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.55  thf(t38_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.19/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.19/0.55         ((r2_hidden @ X55 @ X54)
% 0.19/0.55          | ~ (r1_tarski @ (k2_tarski @ X53 @ X55) @ X54))),
% 0.19/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.55  thf('8', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.19/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.19/0.55         ((r2_hidden @ X53 @ X54)
% 0.19/0.55          | ~ (r1_tarski @ (k2_tarski @ X53 @ X55) @ X54))),
% 0.19/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      (![X53 : $i, X55 : $i, X56 : $i]:
% 0.19/0.55         ((r1_tarski @ (k2_tarski @ X53 @ X55) @ X56)
% 0.19/0.55          | ~ (r2_hidden @ X55 @ X56)
% 0.19/0.55          | ~ (r2_hidden @ X53 @ X56))),
% 0.19/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.55          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['7', '12'])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (![X10 : $i, X12 : $i]:
% 0.19/0.55         (((X10) = (X12))
% 0.19/0.55          | ~ (r1_tarski @ X12 @ X10)
% 0.19/0.55          | ~ (r1_tarski @ X10 @ X12))),
% 0.19/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 0.19/0.55          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['7', '12'])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.19/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.55  thf(l51_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.55  thf('18', plain,
% 0.19/0.55      (![X51 : $i, X52 : $i]:
% 0.19/0.55         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.19/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      (![X51 : $i, X52 : $i]:
% 0.19/0.55         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.19/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.55  thf(t7_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.19/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.55  thf('24', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)], ['3', '21', '22', '23'])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.19/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['25', '26'])).
% 0.19/0.55  thf('28', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.19/0.55      inference('sup+', [status(thm)], ['24', '27'])).
% 0.19/0.55  thf(t69_enumset1, axiom,
% 0.19/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.19/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.19/0.55         ((r2_hidden @ X53 @ X54)
% 0.19/0.55          | ~ (r1_tarski @ (k2_tarski @ X53 @ X55) @ X54))),
% 0.19/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.55  thf('32', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.19/0.55      inference('sup-', [status(thm)], ['28', '31'])).
% 0.19/0.55  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
