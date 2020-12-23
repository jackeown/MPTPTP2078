%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QzyW5yC941

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:44 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  297 ( 394 expanded)
%              Number of equality atoms :   47 (  63 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k2_tarski @ X45 @ X46 )
      = ( k2_xboole_0 @ ( k1_tarski @ X45 ) @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X53: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X51 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X51 @ X52 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X51 ) @ ( k1_setfam_1 @ X52 ) ) )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('10',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49 != X48 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X48 ) )
       != ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('11',plain,(
    ! [X48: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X48 ) )
     != ( k1_tarski @ X48 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X48: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X48 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X53: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X48: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X48 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QzyW5yC941
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.97/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.17  % Solved by: fo/fo7.sh
% 0.97/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.17  % done 1454 iterations in 0.751s
% 0.97/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.17  % SZS output start Refutation
% 0.97/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.97/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.97/1.17  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.97/1.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.97/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.97/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.97/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.97/1.17  thf(t12_setfam_1, conjecture,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.97/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.17    (~( ![A:$i,B:$i]:
% 0.97/1.17        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.97/1.17    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.97/1.17  thf('0', plain,
% 0.97/1.17      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.97/1.17         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(t69_enumset1, axiom,
% 0.97/1.17    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.97/1.17  thf('1', plain, (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.97/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.17  thf(t41_enumset1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( k2_tarski @ A @ B ) =
% 0.97/1.17       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.97/1.17  thf('2', plain,
% 0.97/1.17      (![X45 : $i, X46 : $i]:
% 0.97/1.17         ((k2_tarski @ X45 @ X46)
% 0.97/1.17           = (k2_xboole_0 @ (k1_tarski @ X45) @ (k1_tarski @ X46)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.97/1.17  thf('3', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k2_tarski @ X0 @ X1)
% 0.97/1.17           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['1', '2'])).
% 0.97/1.17  thf('4', plain, (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.97/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.17  thf(t11_setfam_1, axiom,
% 0.97/1.17    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.97/1.17  thf('5', plain, (![X53 : $i]: ((k1_setfam_1 @ (k1_tarski @ X53)) = (X53))),
% 0.97/1.17      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.97/1.17  thf('6', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['4', '5'])).
% 0.97/1.17  thf(t10_setfam_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.97/1.17          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.97/1.17            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.97/1.17  thf('7', plain,
% 0.97/1.17      (![X51 : $i, X52 : $i]:
% 0.97/1.17         (((X51) = (k1_xboole_0))
% 0.97/1.17          | ((k1_setfam_1 @ (k2_xboole_0 @ X51 @ X52))
% 0.97/1.17              = (k3_xboole_0 @ (k1_setfam_1 @ X51) @ (k1_setfam_1 @ X52)))
% 0.97/1.17          | ((X52) = (k1_xboole_0)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.97/1.17  thf('8', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.97/1.17            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.97/1.17          | ((X1) = (k1_xboole_0))
% 0.97/1.17          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['6', '7'])).
% 0.97/1.17  thf('9', plain, (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.97/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.17  thf(t20_zfmisc_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.97/1.17         ( k1_tarski @ A ) ) <=>
% 0.97/1.17       ( ( A ) != ( B ) ) ))).
% 0.97/1.17  thf('10', plain,
% 0.97/1.17      (![X48 : $i, X49 : $i]:
% 0.97/1.17         (((X49) != (X48))
% 0.97/1.17          | ((k4_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X48))
% 0.97/1.17              != (k1_tarski @ X49)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.97/1.17  thf('11', plain,
% 0.97/1.17      (![X48 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X48))
% 0.97/1.17           != (k1_tarski @ X48))),
% 0.97/1.17      inference('simplify', [status(thm)], ['10'])).
% 0.97/1.17  thf(t3_boole, axiom,
% 0.97/1.17    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.97/1.17  thf('12', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.97/1.17      inference('cnf', [status(esa)], [t3_boole])).
% 0.97/1.17  thf(t48_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.97/1.17  thf('13', plain,
% 0.97/1.17      (![X23 : $i, X24 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.97/1.17           = (k3_xboole_0 @ X23 @ X24))),
% 0.97/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.97/1.17  thf('14', plain,
% 0.97/1.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['12', '13'])).
% 0.97/1.17  thf(t2_boole, axiom,
% 0.97/1.17    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.97/1.17  thf('15', plain,
% 0.97/1.17      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.97/1.17      inference('cnf', [status(esa)], [t2_boole])).
% 0.97/1.17  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.97/1.17      inference('demod', [status(thm)], ['14', '15'])).
% 0.97/1.17  thf('17', plain, (![X48 : $i]: ((k1_xboole_0) != (k1_tarski @ X48))),
% 0.97/1.17      inference('demod', [status(thm)], ['11', '16'])).
% 0.97/1.17  thf('18', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['9', '17'])).
% 0.97/1.17  thf('19', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((X1) = (k1_xboole_0))
% 0.97/1.17          | ((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.97/1.17              = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1))))),
% 0.97/1.17      inference('clc', [status(thm)], ['8', '18'])).
% 0.97/1.17  thf('20', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.97/1.17            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.97/1.17          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['3', '19'])).
% 0.97/1.17  thf('21', plain, (![X53 : $i]: ((k1_setfam_1 @ (k1_tarski @ X53)) = (X53))),
% 0.97/1.17      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.97/1.17  thf('22', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.97/1.17          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['20', '21'])).
% 0.97/1.17  thf('23', plain, (![X48 : $i]: ((k1_xboole_0) != (k1_tarski @ X48))),
% 0.97/1.17      inference('demod', [status(thm)], ['11', '16'])).
% 0.97/1.17  thf('24', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.97/1.17      inference('clc', [status(thm)], ['22', '23'])).
% 0.97/1.17  thf('25', plain,
% 0.97/1.17      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.97/1.17      inference('demod', [status(thm)], ['0', '24'])).
% 0.97/1.17  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.97/1.17  
% 0.97/1.17  % SZS output end Refutation
% 0.97/1.17  
% 0.97/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
