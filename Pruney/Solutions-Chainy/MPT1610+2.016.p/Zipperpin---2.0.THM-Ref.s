%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3jSQTdr9ss

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 134 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k9_setfam_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
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
    ! [X9: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X9 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X9 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('9',plain,(
    ! [X9: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X9 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X9 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3jSQTdr9ss
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 8 iterations in 0.009s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
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
% 0.22/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.47  thf('1', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.47  thf(d1_zfmisc_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.47         (~ (r1_tarski @ X3 @ X4)
% 0.22/0.47          | (r2_hidden @ X3 @ X5)
% 0.22/0.47          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.47  thf(redefinition_k9_setfam_1, axiom,
% 0.22/0.47    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.47  thf('4', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         ((r2_hidden @ X3 @ (k9_setfam_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf('6', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '5'])).
% 0.22/0.47  thf(t13_yellow_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.22/0.47         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X9 : $i]:
% 0.22/0.47         (~ (r2_hidden @ k1_xboole_0 @ X9)
% 0.22/0.47          | ((k3_yellow_0 @ (k2_yellow_1 @ X9)) = (k1_xboole_0))
% 0.22/0.47          | (v1_xboole_0 @ X9))),
% 0.22/0.47      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.22/0.47  thf(t7_boole, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (v1_xboole_0 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t7_boole])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X9 : $i]:
% 0.22/0.47         (((k3_yellow_0 @ (k2_yellow_1 @ X9)) = (k1_xboole_0))
% 0.22/0.47          | ~ (r2_hidden @ k1_xboole_0 @ X9))),
% 0.22/0.47      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.47  thf(t4_yellow_1, axiom,
% 0.22/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k2_yellow_1 @ (k9_setfam_1 @ X10)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '12'])).
% 0.22/0.47  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
