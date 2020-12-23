%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7AVqpVIhVg

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  88 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  211 ( 637 expanded)
%              Number of equality atoms :   37 ( 123 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('1',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) )
        = ( k1_tarski @ X34 ) )
      | ( X34 = X35 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('3',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X31 @ X32 ) )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf('12',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34 != X33 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X33 ) )
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('19',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X33 ) )
     != ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf('23',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7AVqpVIhVg
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 46 iterations in 0.023s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(t69_enumset1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('0', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf(t21_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.47         ( k1_xboole_0 ) ) =>
% 0.20/0.47       ( ( A ) = ( B ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.47            ( k1_xboole_0 ) ) =>
% 0.20/0.47          ( ( A ) = ( B ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t20_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.47         ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ( A ) != ( B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X34 : $i, X35 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X35))
% 0.20/0.47            = (k1_tarski @ X34))
% 0.20/0.47          | ((X34) = (X35)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.47  thf('3', plain, ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, (((sk_A) != (sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf(t19_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.47       ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X31 : $i, X32 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ (k1_tarski @ X31) @ (k2_tarski @ X31 @ X32))
% 0.20/0.47           = (k1_tarski @ X31))),
% 0.20/0.47      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0))
% 0.20/0.47           = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0)) = (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['0', '9'])).
% 0.20/0.47  thf('11', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf(t100_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.47           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.47         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf(t5_boole, axiom,
% 0.20/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.47  thf('15', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X33 : $i, X34 : $i]:
% 0.20/0.47         (((X34) != (X33))
% 0.20/0.47          | ((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X33))
% 0.20/0.47              != (k1_tarski @ X34)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X33 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X33))
% 0.20/0.47           != (k1_tarski @ X33))),
% 0.20/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.47  thf('21', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('22', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.47  thf('24', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['16', '23'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.33/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
