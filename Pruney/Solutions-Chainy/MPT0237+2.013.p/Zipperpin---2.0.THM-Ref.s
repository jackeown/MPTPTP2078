%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.89E3vaDUom

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:00 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   41 (  67 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  259 ( 510 expanded)
%              Number of equality atoms :   39 (  73 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X60 ) @ ( k1_tarski @ X61 ) )
        = ( k2_tarski @ X60 @ X61 ) )
      | ( X60 = X61 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X58 ) @ ( k1_tarski @ X59 ) )
      | ( X58 = X59 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('15',plain,(
    ! [X62: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X62 ) )
      = X62 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['12'])).

thf('20',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','18','19','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.89E3vaDUom
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.70/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.91  % Solved by: fo/fo7.sh
% 0.70/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.91  % done 977 iterations in 0.456s
% 0.70/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.91  % SZS output start Refutation
% 0.70/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.70/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.91  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.70/0.91  thf(t32_zfmisc_1, conjecture,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.70/0.91       ( k2_tarski @ A @ B ) ))).
% 0.70/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.91    (~( ![A:$i,B:$i]:
% 0.70/0.91        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.70/0.91          ( k2_tarski @ A @ B ) ) )),
% 0.70/0.91    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.70/0.91  thf('0', plain,
% 0.70/0.91      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 0.70/0.91         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(l51_zfmisc_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.91  thf('1', plain,
% 0.70/0.91      (![X56 : $i, X57 : $i]:
% 0.70/0.91         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.70/0.91      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.70/0.91  thf('2', plain,
% 0.70/0.91      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.70/0.91         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.70/0.91      inference('demod', [status(thm)], ['0', '1'])).
% 0.70/0.91  thf(t29_zfmisc_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( A ) != ( B ) ) =>
% 0.70/0.91       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.70/0.91         ( k2_tarski @ A @ B ) ) ))).
% 0.70/0.91  thf('3', plain,
% 0.70/0.91      (![X60 : $i, X61 : $i]:
% 0.70/0.91         (((k5_xboole_0 @ (k1_tarski @ X60) @ (k1_tarski @ X61))
% 0.70/0.91            = (k2_tarski @ X60 @ X61))
% 0.70/0.91          | ((X60) = (X61)))),
% 0.70/0.91      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.70/0.91  thf(t17_zfmisc_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( A ) != ( B ) ) =>
% 0.70/0.91       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.70/0.91  thf('4', plain,
% 0.70/0.91      (![X58 : $i, X59 : $i]:
% 0.70/0.91         ((r1_xboole_0 @ (k1_tarski @ X58) @ (k1_tarski @ X59))
% 0.70/0.91          | ((X58) = (X59)))),
% 0.70/0.91      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.70/0.91  thf(t83_xboole_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.91  thf('5', plain,
% 0.70/0.91      (![X16 : $i, X17 : $i]:
% 0.70/0.91         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.70/0.91      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.70/0.91  thf('6', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (((X1) = (X0))
% 0.70/0.91          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.70/0.91              = (k1_tarski @ X1)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['4', '5'])).
% 0.70/0.91  thf(t98_xboole_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.70/0.91  thf('7', plain,
% 0.70/0.91      (![X19 : $i, X20 : $i]:
% 0.70/0.91         ((k2_xboole_0 @ X19 @ X20)
% 0.70/0.91           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.70/0.91      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.91  thf('8', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.70/0.91            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.70/0.91          | ((X0) = (X1)))),
% 0.70/0.91      inference('sup+', [status(thm)], ['6', '7'])).
% 0.70/0.91  thf('9', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.70/0.91            = (k2_tarski @ X1 @ X0))
% 0.70/0.91          | ((X1) = (X0))
% 0.70/0.91          | ((X0) = (X1)))),
% 0.70/0.91      inference('sup+', [status(thm)], ['3', '8'])).
% 0.70/0.91  thf('10', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (((X1) = (X0))
% 0.70/0.91          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.70/0.91              = (k2_tarski @ X1 @ X0)))),
% 0.70/0.91      inference('simplify', [status(thm)], ['9'])).
% 0.70/0.91  thf('11', plain,
% 0.70/0.91      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.70/0.91         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.70/0.91      inference('demod', [status(thm)], ['0', '1'])).
% 0.70/0.91  thf('12', plain,
% 0.70/0.91      ((((k2_tarski @ sk_A @ sk_B_1) != (k2_tarski @ sk_A @ sk_B_1))
% 0.70/0.91        | ((sk_A) = (sk_B_1)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.91  thf('13', plain, (((sk_A) = (sk_B_1))),
% 0.70/0.91      inference('simplify', [status(thm)], ['12'])).
% 0.70/0.91  thf(t69_enumset1, axiom,
% 0.70/0.91    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.70/0.91  thf('14', plain,
% 0.70/0.91      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.70/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.70/0.91  thf(t31_zfmisc_1, axiom,
% 0.70/0.91    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.70/0.91  thf('15', plain, (![X62 : $i]: ((k3_tarski @ (k1_tarski @ X62)) = (X62))),
% 0.70/0.91      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.70/0.91  thf('16', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.70/0.91      inference('sup+', [status(thm)], ['14', '15'])).
% 0.70/0.91  thf('17', plain,
% 0.70/0.91      (![X56 : $i, X57 : $i]:
% 0.70/0.91         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.70/0.91      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.70/0.91  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.70/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.91  thf('19', plain, (((sk_A) = (sk_B_1))),
% 0.70/0.91      inference('simplify', [status(thm)], ['12'])).
% 0.70/0.91  thf('20', plain,
% 0.70/0.91      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.70/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.70/0.91  thf('21', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.70/0.91      inference('demod', [status(thm)], ['2', '13', '18', '19', '20'])).
% 0.70/0.91  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.70/0.91  
% 0.70/0.91  % SZS output end Refutation
% 0.70/0.91  
% 0.70/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
