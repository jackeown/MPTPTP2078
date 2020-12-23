%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p67NXcYNU1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:03 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  76 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 ( 583 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X50 ) )
        = ( k2_tarski @ X49 @ X50 ) )
      | ( X49 = X50 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X48 ) )
      | ( X47 = X48 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
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
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('15',plain,(
    ! [X41: $i,X43: $i,X44: $i] :
      ( ( r1_tarski @ X43 @ ( k2_tarski @ X41 @ X44 ) )
      | ( X43
       != ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('16',plain,(
    ! [X41: $i,X44: $i] :
      ( r1_tarski @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X41 @ X44 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf('25',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','23','24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p67NXcYNU1
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:43:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 152 iterations in 0.062s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(t32_zfmisc_1, conjecture,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.19/0.52       ( k2_tarski @ A @ B ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i]:
% 0.19/0.52        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.19/0.52          ( k2_tarski @ A @ B ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.19/0.52         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(l51_zfmisc_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X45 : $i, X46 : $i]:
% 0.19/0.52         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.19/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.52         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf(t29_zfmisc_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( A ) != ( B ) ) =>
% 0.19/0.52       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.52         ( k2_tarski @ A @ B ) ) ))).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X49 : $i, X50 : $i]:
% 0.19/0.52         (((k5_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X50))
% 0.19/0.52            = (k2_tarski @ X49 @ X50))
% 0.19/0.52          | ((X49) = (X50)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.19/0.52  thf(t17_zfmisc_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( A ) != ( B ) ) =>
% 0.19/0.52       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (![X47 : $i, X48 : $i]:
% 0.19/0.52         ((r1_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X48))
% 0.19/0.52          | ((X47) = (X48)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.19/0.52  thf(t83_xboole_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i]:
% 0.19/0.52         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.19/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X1) = (X0))
% 0.19/0.52          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.52              = (k1_tarski @ X1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.52  thf(t98_xboole_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X11 : $i, X12 : $i]:
% 0.19/0.52         ((k2_xboole_0 @ X11 @ X12)
% 0.19/0.52           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.52            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.19/0.52          | ((X0) = (X1)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.52            = (k2_tarski @ X1 @ X0))
% 0.19/0.52          | ((X1) = (X0))
% 0.19/0.52          | ((X0) = (X1)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['3', '8'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X1) = (X0))
% 0.19/0.52          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.52              = (k2_tarski @ X1 @ X0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.52         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.19/0.52        | ((sk_A) = (sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.52  thf('13', plain, (((sk_A) = (sk_B))),
% 0.19/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.52  thf(t69_enumset1, axiom,
% 0.19/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.19/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.52  thf(l45_zfmisc_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.19/0.52       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.19/0.52            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X41 : $i, X43 : $i, X44 : $i]:
% 0.19/0.52         ((r1_tarski @ X43 @ (k2_tarski @ X41 @ X44))
% 0.19/0.52          | ((X43) != (k1_tarski @ X41)))),
% 0.19/0.52      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X41 : $i, X44 : $i]:
% 0.19/0.52         (r1_tarski @ (k1_tarski @ X41) @ (k2_tarski @ X41 @ X44))),
% 0.19/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['14', '16'])).
% 0.19/0.52  thf(l32_xboole_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      (![X2 : $i, X4 : $i]:
% 0.19/0.52         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.19/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      (![X11 : $i, X12 : $i]:
% 0.19/0.52         ((k2_xboole_0 @ X11 @ X12)
% 0.19/0.52           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.19/0.52           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.52  thf(t5_boole, axiom,
% 0.19/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.52  thf('22', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.19/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.19/0.52           = (k1_tarski @ X0))),
% 0.19/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.52  thf('24', plain, (((sk_A) = (sk_B))),
% 0.19/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.19/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.52  thf('26', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['2', '13', '23', '24', '25'])).
% 0.19/0.52  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
