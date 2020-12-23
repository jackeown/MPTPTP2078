%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fOCeaF7bGk

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  223 ( 237 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t61_setfam_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_setfam_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t83_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ X11 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t83_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','6','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fOCeaF7bGk
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:48:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 98 iterations in 0.038s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(t61_setfam_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( m1_subset_1 @
% 0.21/0.50       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( m1_subset_1 @
% 0.21/0.50          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t1_zfmisc_1, axiom,
% 0.21/0.50    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.21/0.50  thf('1', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.50  thf(t83_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) ) =
% 0.21/0.50       ( k3_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         ((k1_zfmisc_1 @ (k3_xboole_0 @ X11 @ X12))
% 0.21/0.50           = (k3_xboole_0 @ (k1_zfmisc_1 @ X11) @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t83_zfmisc_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k1_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.21/0.50           = (k3_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(t48_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.21/0.50           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf(t4_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k1_tarski @ k1_xboole_0)
% 0.21/0.50           = (k3_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.21/0.50           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf(t38_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.21/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.50          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_tarski @ 
% 0.21/0.50             (k4_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)) @ 
% 0.21/0.50             (k1_tarski @ k1_xboole_0))
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))
% 0.21/0.50              = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.50  thf(t36_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))
% 0.21/0.50           = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf(l32_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50          | (r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]: (r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X13 : $i, X15 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
