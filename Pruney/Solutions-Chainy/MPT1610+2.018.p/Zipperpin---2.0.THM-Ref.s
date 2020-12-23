%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PV8oaq4ep3

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 160 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(t18_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow_1])).

thf('0',plain,(
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( k9_setfam_1 @ X7 )
      = ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    ! [X7: $i] :
      ( ( k9_setfam_1 @ X7 )
      = ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['5','8'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X8 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X8 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PV8oaq4ep3
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 10 iterations in 0.011s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.22/0.47  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.22/0.47  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.22/0.47  thf(t18_yellow_1, conjecture,
% 0.22/0.47    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.22/0.47  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t4_subset_1, axiom,
% 0.22/0.47    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.47  thf(redefinition_k9_setfam_1, axiom,
% 0.22/0.47    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.47  thf('2', plain, (![X7 : $i]: ((k9_setfam_1 @ X7) = (k1_zfmisc_1 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X1))),
% 0.22/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf(t2_subset, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i]:
% 0.22/0.47         ((r2_hidden @ X2 @ X3)
% 0.22/0.47          | (v1_xboole_0 @ X3)
% 0.22/0.47          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.22/0.47          | (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf(fc1_subset_1, axiom,
% 0.22/0.47    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.47  thf('6', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.47  thf('7', plain, (![X7 : $i]: ((k9_setfam_1 @ X7) = (k1_zfmisc_1 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.47  thf('8', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.47  thf('9', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.22/0.47      inference('clc', [status(thm)], ['5', '8'])).
% 0.22/0.47  thf(t13_yellow_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.22/0.47         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X8 : $i]:
% 0.22/0.47         (~ (r2_hidden @ k1_xboole_0 @ X8)
% 0.22/0.47          | ((k3_yellow_0 @ (k2_yellow_1 @ X8)) = (k1_xboole_0))
% 0.22/0.47          | (v1_xboole_0 @ X8))),
% 0.22/0.47      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.22/0.47          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf(t4_yellow_1, axiom,
% 0.22/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k2_yellow_1 @ (k9_setfam_1 @ X9)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.22/0.47          | ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0)))),
% 0.22/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.47  thf('14', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.22/0.47      inference('clc', [status(thm)], ['13', '14'])).
% 0.22/0.47  thf('16', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '15'])).
% 0.22/0.47  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
