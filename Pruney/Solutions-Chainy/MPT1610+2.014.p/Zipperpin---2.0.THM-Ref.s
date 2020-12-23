%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nq5croNrZc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 146 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k9_setfam_1 @ X7 )
      = ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k9_setfam_1 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X8 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X8 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('12',plain,(
    ! [X7: $i] :
      ( ( k9_setfam_1 @ X7 )
      = ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nq5croNrZc
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 10 iterations in 0.011s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.47  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.47  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(t18_yellow_1, conjecture,
% 0.21/0.47    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.21/0.47  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('1', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf(d1_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.47          | (r2_hidden @ X1 @ X3)
% 0.21/0.47          | ((X3) != (k1_zfmisc_1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.47  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.47  thf('4', plain, (![X7 : $i]: ((k9_setfam_1 @ X7) = (k1_zfmisc_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ X1 @ (k9_setfam_1 @ X2)) | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '5'])).
% 0.21/0.47  thf(t13_yellow_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.47         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X8 : $i]:
% 0.21/0.47         (~ (r2_hidden @ k1_xboole_0 @ X8)
% 0.21/0.47          | ((k3_yellow_0 @ (k2_yellow_1 @ X8)) = (k1_xboole_0))
% 0.21/0.47          | (v1_xboole_0 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.47          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf(t4_yellow_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k2_yellow_1 @ (k9_setfam_1 @ X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.47          | ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(fc1_subset_1, axiom,
% 0.21/0.47    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.47  thf('11', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.47  thf('12', plain, (![X7 : $i]: ((k9_setfam_1 @ X7) = (k1_zfmisc_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.47  thf('13', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X6))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.21/0.47      inference('clc', [status(thm)], ['10', '13'])).
% 0.21/0.47  thf('15', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.47  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
