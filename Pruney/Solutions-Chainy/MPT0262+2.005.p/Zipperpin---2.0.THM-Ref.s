%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NfFS9cJLqW

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:30 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  317 ( 396 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t57_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ B )
          & ~ ( r2_hidden @ C @ B )
          & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t57_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t114_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ D )
        & ( r1_xboole_0 @ B @ D )
        & ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X1 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t114_xboole_1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X1 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X3 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ ( k1_tarski @ X1 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ X3 @ ( k1_tarski @ X2 ) ) ) @ X0 )
      | ~ ( r1_xboole_0 @ X3 @ X0 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X2 ) ) ) @ X0 )
      | ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_tarski @ X1 @ X2 ) ) @ X0 )
      | ( r2_hidden @ X3 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NfFS9cJLqW
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 342 iterations in 0.202s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.66  thf(t57_zfmisc_1, conjecture,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.45/0.66          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.66        ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.45/0.66             ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t57_zfmisc_1])).
% 0.45/0.66  thf('0', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t69_enumset1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.66  thf('1', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf(t41_enumset1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k2_tarski @ A @ B ) =
% 0.45/0.66       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i]:
% 0.45/0.66         ((k2_tarski @ X7 @ X8)
% 0.45/0.66           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X8)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k2_tarski @ X1 @ X0)
% 0.45/0.66           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf('4', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf(l27_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k1_tarski @ X10) @ X11) | (r2_hidden @ X10 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k1_tarski @ X10) @ X11) | (r2_hidden @ X10 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k1_tarski @ X10) @ X11) | (r2_hidden @ X10 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.45/0.66  thf(t114_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 0.45/0.66         ( r1_xboole_0 @ C @ D ) ) =>
% 0.45/0.66       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ X3)
% 0.45/0.66          | ~ (r1_xboole_0 @ X2 @ X3)
% 0.45/0.66          | ~ (r1_xboole_0 @ X1 @ X3)
% 0.45/0.66          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [t114_xboole_1])).
% 0.45/0.66  thf(t4_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.66       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.45/0.66           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)) @ X3)
% 0.45/0.66          | ~ (r1_xboole_0 @ X2 @ X3)
% 0.45/0.66          | ~ (r1_xboole_0 @ X1 @ X3)
% 0.45/0.66          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((r2_hidden @ X1 @ X0)
% 0.45/0.66          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.45/0.66          | ~ (r1_xboole_0 @ X3 @ X0)
% 0.45/0.66          | (r1_xboole_0 @ 
% 0.45/0.66             (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ (k1_tarski @ X1))) @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['8', '11'])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((r2_hidden @ X1 @ X0)
% 0.45/0.66          | (r1_xboole_0 @ 
% 0.45/0.66             (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.45/0.66              (k2_xboole_0 @ X3 @ (k1_tarski @ X2))) @ 
% 0.45/0.66             X0)
% 0.45/0.66          | ~ (r1_xboole_0 @ X3 @ X0)
% 0.45/0.66          | (r2_hidden @ X2 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['7', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((r2_hidden @ X1 @ X0)
% 0.45/0.66          | (r2_hidden @ X2 @ X0)
% 0.45/0.66          | (r1_xboole_0 @ 
% 0.45/0.66             (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.45/0.66              (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X2))) @ 
% 0.45/0.66             X0)
% 0.45/0.66          | (r2_hidden @ X3 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '13'])).
% 0.45/0.66  thf('15', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i]:
% 0.45/0.66         ((k2_tarski @ X7 @ X8)
% 0.45/0.66           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X8)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k2_tarski @ X0 @ X1)
% 0.45/0.66           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((r2_hidden @ X1 @ X0)
% 0.45/0.66          | (r2_hidden @ X2 @ X0)
% 0.45/0.66          | (r1_xboole_0 @ 
% 0.45/0.66             (k2_xboole_0 @ (k1_tarski @ X3) @ (k2_tarski @ X1 @ X2)) @ X0)
% 0.45/0.66          | (r2_hidden @ X3 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['14', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.45/0.66          | (r2_hidden @ X1 @ X2)
% 0.45/0.66          | (r2_hidden @ X0 @ X2)
% 0.45/0.66          | (r2_hidden @ X0 @ X2))),
% 0.45/0.66      inference('sup+', [status(thm)], ['3', '18'])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((r2_hidden @ X0 @ X2)
% 0.45/0.66          | (r2_hidden @ X1 @ X2)
% 0.45/0.66          | (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.45/0.66      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.66  thf('21', plain, (~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('22', plain, (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_C @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('24', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.45/0.66      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.66  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
