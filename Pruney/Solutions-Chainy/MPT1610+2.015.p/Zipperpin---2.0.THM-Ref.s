%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.paAqOxfNZb

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  46 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  181 ( 196 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k9_setfam_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k9_setfam_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X14 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X14 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('19',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['16','19'])).

thf('21',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.paAqOxfNZb
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:47:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 16 iterations in 0.014s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.48  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(t18_yellow_1, conjecture,
% 0.21/0.48    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.21/0.48  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t4_subset_1, axiom,
% 0.21/0.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.48  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.48  thf('2', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X6))),
% 0.21/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf(t3_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.48  thf('5', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k9_setfam_1 @ X8)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.48  thf(d1_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.48          | (r2_hidden @ X0 @ X2)
% 0.21/0.48          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf('10', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ (k9_setfam_1 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.48  thf(t13_yellow_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.48         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X14 : $i]:
% 0.21/0.48         (~ (r2_hidden @ k1_xboole_0 @ X14)
% 0.21/0.48          | ((k3_yellow_0 @ (k2_yellow_1 @ X14)) = (k1_xboole_0))
% 0.21/0.48          | (v1_xboole_0 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.48          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(t4_yellow_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k2_yellow_1 @ (k9_setfam_1 @ X15)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.48          | ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf(fc1_subset_1, axiom,
% 0.21/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.48  thf('17', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.48  thf('18', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.48  thf('19', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X5))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['16', '19'])).
% 0.21/0.48  thf('21', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '20'])).
% 0.21/0.48  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
