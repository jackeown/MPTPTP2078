%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FwhzNop57J

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  213 ( 235 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X38: $i] :
      ( ( r1_tarski @ X38 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t22_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t22_relat_1])).

thf('11',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FwhzNop57J
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 32 iterations in 0.023s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(t21_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) =>
% 0.19/0.47       ( r1_tarski @
% 0.19/0.47         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X38 : $i]:
% 0.19/0.47         ((r1_tarski @ X38 @ 
% 0.19/0.47           (k2_zfmisc_1 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 0.19/0.47          | ~ (v1_relat_1 @ X38))),
% 0.19/0.47      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.19/0.47  thf(t12_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ X0)
% 0.19/0.47          | ((k2_xboole_0 @ X0 @ 
% 0.19/0.47              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.19/0.47              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf(t95_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k3_xboole_0 @ A @ B ) =
% 0.19/0.47       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         ((k3_xboole_0 @ X7 @ X8)
% 0.19/0.47           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k2_xboole_0 @ X7 @ X8)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.19/0.47  thf(t91_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.47       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 0.19/0.47           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         ((k3_xboole_0 @ X7 @ X8)
% 0.19/0.47           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k3_xboole_0 @ X0 @ 
% 0.19/0.47            (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.19/0.47            = (k5_xboole_0 @ X0 @ 
% 0.19/0.47               (k5_xboole_0 @ 
% 0.19/0.47                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ 
% 0.19/0.47                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['2', '5'])).
% 0.19/0.47  thf(t92_xboole_1, axiom,
% 0.19/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('7', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k3_xboole_0 @ X0 @ 
% 0.19/0.47            (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.19/0.47            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf(t5_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('9', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k3_xboole_0 @ X0 @ 
% 0.19/0.47            (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))) = (X0))
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf(t22_relat_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) =>
% 0.19/0.47       ( ( k3_xboole_0 @
% 0.19/0.47           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.19/0.47         ( A ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( v1_relat_1 @ A ) =>
% 0.19/0.47          ( ( k3_xboole_0 @
% 0.19/0.47              A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.19/0.47            ( A ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t22_relat_1])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (((k3_xboole_0 @ sk_A @ 
% 0.19/0.47         (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) != (
% 0.19/0.47         sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('12', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.47  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('14', plain, (((sk_A) != (sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
