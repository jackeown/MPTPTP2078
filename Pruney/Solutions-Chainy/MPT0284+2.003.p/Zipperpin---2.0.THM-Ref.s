%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G7U3T0Dbqv

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:47 EST 2020

% Result     : Theorem 10.44s
% Output     : Refutation 10.44s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  266 ( 316 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t86_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G7U3T0Dbqv
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 10.44/10.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.44/10.66  % Solved by: fo/fo7.sh
% 10.44/10.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.44/10.66  % done 9017 iterations in 10.208s
% 10.44/10.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.44/10.66  % SZS output start Refutation
% 10.44/10.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 10.44/10.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.44/10.66  thf(sk_B_type, type, sk_B: $i).
% 10.44/10.66  thf(sk_A_type, type, sk_A: $i).
% 10.44/10.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.44/10.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.44/10.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 10.44/10.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 10.44/10.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 10.44/10.66  thf(t86_zfmisc_1, conjecture,
% 10.44/10.66    (![A:$i,B:$i]:
% 10.44/10.66     ( r1_tarski @
% 10.44/10.66       ( k2_xboole_0 @
% 10.44/10.66         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 10.44/10.66         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 10.44/10.66       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 10.44/10.66  thf(zf_stmt_0, negated_conjecture,
% 10.44/10.66    (~( ![A:$i,B:$i]:
% 10.44/10.66        ( r1_tarski @
% 10.44/10.66          ( k2_xboole_0 @
% 10.44/10.66            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 10.44/10.66            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 10.44/10.66          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 10.44/10.66    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 10.44/10.66  thf('0', plain,
% 10.44/10.66      (~ (r1_tarski @ 
% 10.44/10.66          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 10.44/10.66           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 10.44/10.66          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 10.44/10.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.44/10.66  thf(d6_xboole_0, axiom,
% 10.44/10.66    (![A:$i,B:$i]:
% 10.44/10.66     ( ( k5_xboole_0 @ A @ B ) =
% 10.44/10.66       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 10.44/10.66  thf('1', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]:
% 10.44/10.66         ((k5_xboole_0 @ X0 @ X1)
% 10.44/10.66           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 10.44/10.66      inference('cnf', [status(esa)], [d6_xboole_0])).
% 10.44/10.66  thf(commutativity_k2_tarski, axiom,
% 10.44/10.66    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 10.44/10.66  thf('2', plain,
% 10.44/10.66      (![X13 : $i, X14 : $i]:
% 10.44/10.66         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 10.44/10.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 10.44/10.66  thf(l51_zfmisc_1, axiom,
% 10.44/10.66    (![A:$i,B:$i]:
% 10.44/10.66     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 10.44/10.66  thf('3', plain,
% 10.44/10.66      (![X17 : $i, X18 : $i]:
% 10.44/10.66         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 10.44/10.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 10.44/10.66  thf('4', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]:
% 10.44/10.66         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 10.44/10.66      inference('sup+', [status(thm)], ['2', '3'])).
% 10.44/10.66  thf('5', plain,
% 10.44/10.66      (![X17 : $i, X18 : $i]:
% 10.44/10.66         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 10.44/10.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 10.44/10.66  thf('6', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.44/10.66      inference('sup+', [status(thm)], ['4', '5'])).
% 10.44/10.66  thf(d10_xboole_0, axiom,
% 10.44/10.66    (![A:$i,B:$i]:
% 10.44/10.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.44/10.66  thf('7', plain,
% 10.44/10.66      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 10.44/10.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.44/10.66  thf('8', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 10.44/10.66      inference('simplify', [status(thm)], ['7'])).
% 10.44/10.66  thf(t11_xboole_1, axiom,
% 10.44/10.66    (![A:$i,B:$i,C:$i]:
% 10.44/10.66     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 10.44/10.66  thf('9', plain,
% 10.44/10.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 10.44/10.66         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 10.44/10.66      inference('cnf', [status(esa)], [t11_xboole_1])).
% 10.44/10.66  thf('10', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 10.44/10.66      inference('sup-', [status(thm)], ['8', '9'])).
% 10.44/10.66  thf('11', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 10.44/10.66      inference('sup+', [status(thm)], ['6', '10'])).
% 10.44/10.66  thf(t79_zfmisc_1, axiom,
% 10.44/10.66    (![A:$i,B:$i]:
% 10.44/10.66     ( ( r1_tarski @ A @ B ) =>
% 10.44/10.66       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 10.44/10.66  thf('12', plain,
% 10.44/10.66      (![X19 : $i, X20 : $i]:
% 10.44/10.66         ((r1_tarski @ (k1_zfmisc_1 @ X19) @ (k1_zfmisc_1 @ X20))
% 10.44/10.66          | ~ (r1_tarski @ X19 @ X20))),
% 10.44/10.66      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 10.44/10.66  thf('13', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]:
% 10.44/10.66         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 10.44/10.66          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.44/10.66      inference('sup-', [status(thm)], ['11', '12'])).
% 10.44/10.66  thf('14', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 10.44/10.66      inference('sup-', [status(thm)], ['8', '9'])).
% 10.44/10.66  thf('15', plain,
% 10.44/10.66      (![X19 : $i, X20 : $i]:
% 10.44/10.66         ((r1_tarski @ (k1_zfmisc_1 @ X19) @ (k1_zfmisc_1 @ X20))
% 10.44/10.66          | ~ (r1_tarski @ X19 @ X20))),
% 10.44/10.66      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 10.44/10.66  thf('16', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]:
% 10.44/10.66         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 10.44/10.66          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.44/10.66      inference('sup-', [status(thm)], ['14', '15'])).
% 10.44/10.66  thf(t8_xboole_1, axiom,
% 10.44/10.66    (![A:$i,B:$i,C:$i]:
% 10.44/10.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 10.44/10.66       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 10.44/10.66  thf('17', plain,
% 10.44/10.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.44/10.66         (~ (r1_tarski @ X10 @ X11)
% 10.44/10.66          | ~ (r1_tarski @ X12 @ X11)
% 10.44/10.66          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 10.44/10.66      inference('cnf', [status(esa)], [t8_xboole_1])).
% 10.44/10.66  thf('18', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.44/10.66         ((r1_tarski @ (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 10.44/10.66           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 10.44/10.66          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 10.44/10.66      inference('sup-', [status(thm)], ['16', '17'])).
% 10.44/10.66  thf('19', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]:
% 10.44/10.66         (r1_tarski @ 
% 10.44/10.66          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 10.44/10.66          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.44/10.66      inference('sup-', [status(thm)], ['13', '18'])).
% 10.44/10.66  thf('20', plain,
% 10.44/10.66      (![X0 : $i, X1 : $i]:
% 10.44/10.66         (r1_tarski @ 
% 10.44/10.66          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 10.44/10.66           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 10.44/10.66          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 10.44/10.66      inference('sup+', [status(thm)], ['1', '19'])).
% 10.44/10.66  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 10.44/10.66  
% 10.44/10.66  % SZS output end Refutation
% 10.44/10.66  
% 10.44/10.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
