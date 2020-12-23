%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5u5Dz4INIy

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  214 ( 244 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t19_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_1])).

thf('0',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k9_setfam_1 @ X12 )
      = ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X13 ) @ X13 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X13 ) )
        = ( k3_tarski @ X13 ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X13: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X13 ) )
        = ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X13 ) @ X13 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k9_setfam_1 @ X12 )
      = ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k9_setfam_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k9_setfam_1 @ X12 )
      = ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('18',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['15','18'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k3_yellow_1 @ X14 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','19','20','21'])).

thf('23',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5u5Dz4INIy
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 20 iterations in 0.012s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.47  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.47  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(t19_yellow_1, conjecture,
% 0.20/0.47    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.20/0.47  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t99_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.47  thf('1', plain, (![X4 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X4)) = (X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.47  thf(redefinition_k9_setfam_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.47  thf('2', plain, (![X12 : $i]: ((k9_setfam_1 @ X12) = (k1_zfmisc_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('3', plain, (![X4 : $i]: ((k3_tarski @ (k9_setfam_1 @ X4)) = (X4))),
% 0.20/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(t14_yellow_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.20/0.47         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X13 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (k3_tarski @ X13) @ X13)
% 0.20/0.47          | ((k4_yellow_0 @ (k2_yellow_1 @ X13)) = (k3_tarski @ X13))
% 0.20/0.47          | (v1_xboole_0 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.20/0.47  thf(d1_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X13 : $i]:
% 0.20/0.47         (((k4_yellow_0 @ (k2_yellow_1 @ X13)) = (k3_tarski @ X13))
% 0.20/0.47          | ~ (r2_hidden @ (k3_tarski @ X13) @ X13))),
% 0.20/0.47      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.20/0.47          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.20/0.47              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.47  thf(t3_boole, axiom,
% 0.20/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.47  thf('8', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.47  thf(dt_k6_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (m1_subset_1 @ (k6_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.20/0.47  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.47  thf('11', plain, (![X12 : $i]: ((k9_setfam_1 @ X12) = (k1_zfmisc_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (m1_subset_1 @ (k4_xboole_0 @ X5 @ X6) @ (k9_setfam_1 @ X5))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.47  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k9_setfam_1 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['8', '12'])).
% 0.20/0.47  thf(t2_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         ((r2_hidden @ X10 @ X11)
% 0.20/0.47          | (v1_xboole_0 @ X11)
% 0.20/0.47          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.20/0.47          | (r2_hidden @ X0 @ (k9_setfam_1 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(fc1_subset_1, axiom,
% 0.20/0.47    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.47  thf('16', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.47  thf('17', plain, (![X12 : $i]: ((k9_setfam_1 @ X12) = (k1_zfmisc_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('18', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X7))),
% 0.20/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.20/0.47      inference('clc', [status(thm)], ['15', '18'])).
% 0.20/0.47  thf(t4_yellow_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X14 : $i]: ((k3_yellow_1 @ X14) = (k2_yellow_1 @ (k9_setfam_1 @ X14)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.47  thf('21', plain, (![X4 : $i]: ((k3_tarski @ (k9_setfam_1 @ X4)) = (X4))),
% 0.20/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('22', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '19', '20', '21'])).
% 0.20/0.47  thf('23', plain, (((sk_A) != (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '22'])).
% 0.20/0.47  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
