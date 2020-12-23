%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fov8ueIAT9

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:31 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 105 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  438 ( 836 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

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

thf('1',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_xboole_0 @ X41 @ ( k1_tarski @ X40 ) )
        = ( k1_tarski @ X40 ) )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t55_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('22',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('24',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','22','23'])).

thf('25',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('33',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fov8ueIAT9
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 250 iterations in 0.234s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.67  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(l27_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (![X38 : $i, X39 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ (k1_tarski @ X38) @ X39) | (r2_hidden @ X38 @ X39))),
% 0.46/0.67      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.46/0.67  thf(t58_zfmisc_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.46/0.67       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i]:
% 0.46/0.67        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.46/0.67          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.46/0.67  thf('1', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf(l31_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.67       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X40 : $i, X41 : $i]:
% 0.46/0.67         (((k3_xboole_0 @ X41 @ (k1_tarski @ X40)) = (k1_tarski @ X40))
% 0.46/0.67          | ~ (r2_hidden @ X40 @ X41))),
% 0.46/0.67      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf(t100_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X2 : $i, X3 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ X2 @ X3)
% 0.46/0.67           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.67         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf(t55_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 0.46/0.67       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X7 : $i, X8 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 0.46/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k4_xboole_0 @ X8 @ X7)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t55_xboole_1])).
% 0.46/0.67  thf(l98_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k5_xboole_0 @ A @ B ) =
% 0.46/0.67       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k5_xboole_0 @ X0 @ X1)
% 0.46/0.67           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k5_xboole_0 @ X0 @ X1)
% 0.46/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.67         = (k2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.46/0.67            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['6', '9'])).
% 0.46/0.67  thf(commutativity_k2_tarski, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i]:
% 0.46/0.67         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.46/0.67      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.67  thf(l51_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X42 : $i, X43 : $i]:
% 0.46/0.67         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.46/0.67      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      (![X42 : $i, X43 : $i]:
% 0.46/0.67         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.46/0.67      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.67         = (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.67            (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['10', '15'])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X7 : $i, X8 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 0.46/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k4_xboole_0 @ X8 @ X7)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t55_xboole_1])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.67         (k1_tarski @ sk_A))
% 0.46/0.67         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.67            (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k5_xboole_0 @ X0 @ X1)
% 0.46/0.67           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.67         = (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.67            (k1_tarski @ sk_A)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.67         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.67         = (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.67            (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['19', '22', '23'])).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.67         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.67      inference('sup+', [status(thm)], ['16', '24'])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf(t95_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k3_xboole_0 @ A @ B ) =
% 0.46/0.67       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (![X9 : $i, X10 : $i]:
% 0.46/0.67         ((k3_xboole_0 @ X9 @ X10)
% 0.46/0.67           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k3_xboole_0 @ X0 @ X1)
% 0.46/0.67           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.67         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.67            (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['25', '28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X9 : $i, X10 : $i]:
% 0.46/0.67         ((k3_xboole_0 @ X9 @ X10)
% 0.46/0.67           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.67         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('35', plain, ($false),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
