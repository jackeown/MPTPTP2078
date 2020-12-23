%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qQuvLMB1FY

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  53 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  285 ( 377 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
      | ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('19',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_xboole_0 @ X40 @ ( k1_tarski @ X39 ) )
        = ( k1_tarski @ X39 ) )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','17','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qQuvLMB1FY
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:23:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 111 iterations in 0.134s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.59  thf(t58_zfmisc_1, conjecture,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.20/0.59       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i,B:$i]:
% 0.20/0.59        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.20/0.59          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(commutativity_k2_tarski, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.59  thf(l51_zfmisc_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      (![X41 : $i, X42 : $i]:
% 0.20/0.59         ((k3_tarski @ (k2_tarski @ X41 @ X42)) = (k2_xboole_0 @ X41 @ X42))),
% 0.20/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (![X41 : $i, X42 : $i]:
% 0.20/0.59         ((k3_tarski @ (k2_tarski @ X41 @ X42)) = (k2_xboole_0 @ X41 @ X42))),
% 0.20/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.59  thf(t95_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.59       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (![X5 : $i, X6 : $i]:
% 0.20/0.59         ((k3_xboole_0 @ X5 @ X6)
% 0.20/0.59           = (k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.59  thf(t91_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.59       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.59  thf('7', plain,
% 0.20/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.59           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (![X5 : $i, X6 : $i]:
% 0.20/0.59         ((k3_xboole_0 @ X5 @ X6)
% 0.20/0.59           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ (k2_xboole_0 @ X5 @ X6))))),
% 0.20/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k3_xboole_0 @ X0 @ X1)
% 0.20/0.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.20/0.59      inference('sup+', [status(thm)], ['5', '8'])).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      (![X5 : $i, X6 : $i]:
% 0.20/0.59         ((k3_xboole_0 @ X5 @ X6)
% 0.20/0.59           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ (k2_xboole_0 @ X5 @ X6))))),
% 0.20/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.59           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.59  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.20/0.59           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k3_xboole_0 @ X1 @ X0)
% 0.20/0.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k3_xboole_0 @ X1 @ X0)
% 0.20/0.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.20/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['9', '16'])).
% 0.20/0.59  thf(l27_zfmisc_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X37 : $i, X38 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ (k1_tarski @ X37) @ X38) | (r2_hidden @ X37 @ X38))),
% 0.20/0.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.59  thf('19', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('20', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.59  thf(l31_zfmisc_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.59       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X39 : $i, X40 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ X40 @ (k1_tarski @ X39)) = (k1_tarski @ X39))
% 0.20/0.59          | ~ (r2_hidden @ X39 @ X40))),
% 0.20/0.59      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('23', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['0', '17', '22'])).
% 0.20/0.59  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
