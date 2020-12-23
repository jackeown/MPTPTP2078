%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.akTOEHbv6a

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  266 ( 314 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_wellord1 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_wellord1 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_wellord1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_wellord1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_wellord1 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t26_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
          = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_wellord1])).

thf('12',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
     != ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.akTOEHbv6a
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:31:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 15 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(d6_wellord1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( k2_wellord1 @ A @ B ) =
% 0.21/0.47           ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (((k2_wellord1 @ X11 @ X12)
% 0.21/0.47            = (k3_xboole_0 @ X11 @ (k2_zfmisc_1 @ X12 @ X12)))
% 0.21/0.47          | ~ (v1_relat_1 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.21/0.47  thf(t16_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.47       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.47           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ (k2_wellord1 @ X1 @ X0) @ X2)
% 0.21/0.47            = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0) @ X2)))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(t123_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.21/0.47       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         ((k2_zfmisc_1 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X8))
% 0.21/0.47           = (k3_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6) @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (((k2_wellord1 @ X11 @ X12)
% 0.21/0.47            = (k3_xboole_0 @ X11 @ (k2_zfmisc_1 @ X12 @ X12)))
% 0.21/0.47          | ~ (v1_relat_1 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.47            = (k3_xboole_0 @ X2 @ 
% 0.21/0.47               (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X1) @ (k2_zfmisc_1 @ X0 @ X0))))
% 0.21/0.47          | ~ (v1_relat_1 @ X2))),
% 0.21/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.47            = (k3_xboole_0 @ (k2_wellord1 @ X2 @ X1) @ (k2_zfmisc_1 @ X0 @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ X2))),
% 0.21/0.47      inference('sup+', [status(thm)], ['2', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X2)
% 0.21/0.47          | ((k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.47              = (k3_xboole_0 @ (k2_wellord1 @ X2 @ X1) @ 
% 0.21/0.47                 (k2_zfmisc_1 @ X0 @ X0))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (((k2_wellord1 @ X11 @ X12)
% 0.21/0.47            = (k3_xboole_0 @ X11 @ (k2_zfmisc_1 @ X12 @ X12)))
% 0.21/0.47          | ~ (v1_relat_1 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.21/0.47            = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ (k2_wellord1 @ X2 @ X1)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(dt_k2_wellord1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k2_wellord1 @ X13 @ X14)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X2)
% 0.21/0.47          | ((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.21/0.47              = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.21/0.47      inference('clc', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf(t26_wellord1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ C ) =>
% 0.21/0.47       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.21/0.47         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ C ) =>
% 0.21/0.47          ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.21/0.47            ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t26_wellord1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.47         != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.47          != (k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.47         != (k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
