%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Px38aJKxeR

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:49 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  241 ( 256 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X23 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X23 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k5_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Px38aJKxeR
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:41:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.68/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.92  % Solved by: fo/fo7.sh
% 0.68/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.92  % done 640 iterations in 0.451s
% 0.68/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.92  % SZS output start Refutation
% 0.68/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.92  thf(t86_zfmisc_1, conjecture,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( r1_tarski @
% 0.68/0.92       ( k2_xboole_0 @
% 0.68/0.92         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.68/0.92         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.68/0.92       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 0.68/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.92    (~( ![A:$i,B:$i]:
% 0.68/0.92        ( r1_tarski @
% 0.68/0.92          ( k2_xboole_0 @
% 0.68/0.92            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.68/0.92            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.68/0.92          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 0.68/0.92    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 0.68/0.92  thf('0', plain,
% 0.68/0.92      (~ (r1_tarski @ 
% 0.68/0.92          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.68/0.92           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 0.68/0.92          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf(t98_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.68/0.92  thf('1', plain,
% 0.68/0.92      (![X14 : $i, X15 : $i]:
% 0.68/0.92         ((k2_xboole_0 @ X14 @ X15)
% 0.68/0.92           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.68/0.92  thf(commutativity_k5_xboole_0, axiom,
% 0.68/0.92    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.68/0.92  thf('2', plain,
% 0.68/0.92      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.92      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.92  thf(t96_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.68/0.92  thf('3', plain,
% 0.68/0.92      (![X12 : $i, X13 : $i]:
% 0.68/0.92         (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ (k5_xboole_0 @ X12 @ X13))),
% 0.68/0.92      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.68/0.92  thf('4', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))),
% 0.68/0.92      inference('sup+', [status(thm)], ['2', '3'])).
% 0.68/0.92  thf(t79_zfmisc_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( r1_tarski @ A @ B ) =>
% 0.68/0.92       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.68/0.92  thf('5', plain,
% 0.68/0.92      (![X23 : $i, X24 : $i]:
% 0.68/0.92         ((r1_tarski @ (k1_zfmisc_1 @ X23) @ (k1_zfmisc_1 @ X24))
% 0.68/0.92          | ~ (r1_tarski @ X23 @ X24))),
% 0.68/0.92      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.68/0.92  thf('6', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 0.68/0.92          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.92  thf(t109_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i]:
% 0.68/0.92     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.68/0.92  thf('7', plain,
% 0.68/0.92      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.92         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 0.68/0.92      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.68/0.92  thf('8', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (r1_tarski @ 
% 0.68/0.92          (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ X2) @ 
% 0.68/0.92          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.68/0.92  thf('9', plain,
% 0.68/0.92      (![X12 : $i, X13 : $i]:
% 0.68/0.92         (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ (k5_xboole_0 @ X12 @ X13))),
% 0.68/0.92      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.68/0.92  thf('10', plain,
% 0.68/0.92      (![X23 : $i, X24 : $i]:
% 0.68/0.92         ((r1_tarski @ (k1_zfmisc_1 @ X23) @ (k1_zfmisc_1 @ X24))
% 0.68/0.92          | ~ (r1_tarski @ X23 @ X24))),
% 0.68/0.92      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.68/0.92  thf('11', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.68/0.92          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.92  thf(t110_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i]:
% 0.68/0.92     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.68/0.92       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.68/0.92  thf('12', plain,
% 0.68/0.92      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.68/0.92         (~ (r1_tarski @ X9 @ X10)
% 0.68/0.92          | ~ (r1_tarski @ X11 @ X10)
% 0.68/0.92          | (r1_tarski @ (k5_xboole_0 @ X9 @ X11) @ X10))),
% 0.68/0.92      inference('cnf', [status(esa)], [t110_xboole_1])).
% 0.68/0.92  thf('13', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         ((r1_tarski @ 
% 0.68/0.92           (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 0.68/0.92           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 0.68/0.92          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['11', '12'])).
% 0.68/0.92  thf('14', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (r1_tarski @ 
% 0.68/0.92          (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.68/0.92           (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ X2)) @ 
% 0.68/0.92          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['8', '13'])).
% 0.68/0.92  thf('15', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ 
% 0.68/0.92          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 0.68/0.92           (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 0.68/0.92          (k1_zfmisc_1 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['1', '14'])).
% 0.68/0.92  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.68/0.92  
% 0.68/0.92  % SZS output end Refutation
% 0.68/0.92  
% 0.68/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
