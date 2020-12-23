%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vdy2zajfz5

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:49 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  122 ( 130 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X8 @ X9 ) @ ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( ( k3_relat_1 @ X7 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('6',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t63_relat_1,conjecture,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t63_relat_1])).

thf('10',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference(clc,[status(thm)],['3','11'])).

thf('13',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vdy2zajfz5
% 0.16/0.37  % Computer   : n009.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 11:56:11 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.25/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.49  % Solved by: fo/fo7.sh
% 0.25/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.49  % done 10 iterations in 0.009s
% 0.25/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.49  % SZS output start Refutation
% 0.25/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.25/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.25/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.25/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.49  thf(fc7_relat_1, axiom,
% 0.25/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.49     ( v1_relat_1 @
% 0.25/0.49       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.25/0.49  thf('0', plain,
% 0.25/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.25/0.49         (v1_relat_1 @ 
% 0.25/0.49          (k2_tarski @ (k4_tarski @ X8 @ X9) @ (k4_tarski @ X10 @ X11)))),
% 0.25/0.49      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.25/0.49  thf(t4_subset_1, axiom,
% 0.25/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.25/0.49  thf('1', plain,
% 0.25/0.49      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.25/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.25/0.49  thf(cc2_relat_1, axiom,
% 0.25/0.49    (![A:$i]:
% 0.25/0.49     ( ( v1_relat_1 @ A ) =>
% 0.25/0.49       ( ![B:$i]:
% 0.25/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.25/0.49  thf('2', plain,
% 0.25/0.49      (![X5 : $i, X6 : $i]:
% 0.25/0.49         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.25/0.49          | (v1_relat_1 @ X5)
% 0.25/0.49          | ~ (v1_relat_1 @ X6))),
% 0.25/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.25/0.49  thf('3', plain,
% 0.25/0.49      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.25/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.49  thf(t60_relat_1, axiom,
% 0.25/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.25/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.25/0.49  thf('4', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.25/0.49  thf(d6_relat_1, axiom,
% 0.25/0.49    (![A:$i]:
% 0.25/0.49     ( ( v1_relat_1 @ A ) =>
% 0.25/0.49       ( ( k3_relat_1 @ A ) =
% 0.25/0.49         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.25/0.49  thf('5', plain,
% 0.25/0.49      (![X7 : $i]:
% 0.25/0.49         (((k3_relat_1 @ X7)
% 0.25/0.49            = (k2_xboole_0 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.25/0.49          | ~ (v1_relat_1 @ X7))),
% 0.25/0.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.25/0.49  thf('6', plain,
% 0.25/0.49      ((((k3_relat_1 @ k1_xboole_0)
% 0.25/0.49          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 0.25/0.49        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.25/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.25/0.49  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.25/0.49  thf(t1_boole, axiom,
% 0.25/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.25/0.49  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.25/0.49  thf('9', plain,
% 0.25/0.49      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.25/0.49        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.25/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.25/0.49  thf(t63_relat_1, conjecture,
% 0.25/0.49    (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.25/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.49    (( k3_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.25/0.49    inference('cnf.neg', [status(esa)], [t63_relat_1])).
% 0.25/0.49  thf('10', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('11', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.25/0.49      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.25/0.49  thf('12', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.25/0.49      inference('clc', [status(thm)], ['3', '11'])).
% 0.25/0.49  thf('13', plain, ($false), inference('sup-', [status(thm)], ['0', '12'])).
% 0.25/0.49  
% 0.25/0.49  % SZS output end Refutation
% 0.25/0.49  
% 0.25/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
