%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VJFnVFd1TQ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  46 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  180 ( 187 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(np__0_type,type,(
    np__0: $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k9_setfam_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ X1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X14 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X14 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X14: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X14 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X14 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(spc0_boole,axiom,(
    v1_xboole_0 @ np__0 )).

thf('13',plain,(
    v1_xboole_0 @ np__0 ),
    inference(cnf,[status(esa)],[spc0_boole])).

thf('14',plain,(
    v1_xboole_0 @ np__0 ),
    inference(cnf,[status(esa)],[spc0_boole])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    np__0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','16'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','17','18'])).

thf('20',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VJFnVFd1TQ
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 25 iterations in 0.009s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.45  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.22/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.45  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.22/0.45  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.22/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.45  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(np__0_type, type, np__0: $i).
% 0.22/0.45  thf(t18_yellow_1, conjecture,
% 0.22/0.45    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.22/0.45  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(d3_tarski, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X4 : $i, X6 : $i]:
% 0.22/0.45         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.22/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.45  thf(d1_xboole_0, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.45  thf(d1_zfmisc_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.45  thf('4', plain,
% 0.22/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.45         (~ (r1_tarski @ X8 @ X9)
% 0.22/0.45          | (r2_hidden @ X8 @ X10)
% 0.22/0.45          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.22/0.45      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.45  thf('5', plain,
% 0.22/0.45      (![X8 : $i, X9 : $i]:
% 0.22/0.45         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.45  thf(redefinition_k9_setfam_1, axiom,
% 0.22/0.45    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.45  thf('6', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.22/0.45      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.45  thf('7', plain,
% 0.22/0.45      (![X8 : $i, X9 : $i]:
% 0.22/0.45         ((r2_hidden @ X8 @ (k9_setfam_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.45  thf('8', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (~ (v1_xboole_0 @ X1) | (r2_hidden @ X1 @ (k9_setfam_1 @ X0)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['3', '7'])).
% 0.22/0.45  thf(t13_yellow_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.45       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.22/0.45         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.45  thf('9', plain,
% 0.22/0.45      (![X14 : $i]:
% 0.22/0.45         (~ (r2_hidden @ k1_xboole_0 @ X14)
% 0.22/0.45          | ((k3_yellow_0 @ (k2_yellow_1 @ X14)) = (k1_xboole_0))
% 0.22/0.45          | (v1_xboole_0 @ X14))),
% 0.22/0.45      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.22/0.45  thf('10', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.45  thf('11', plain,
% 0.22/0.45      (![X14 : $i]:
% 0.22/0.45         (((k3_yellow_0 @ (k2_yellow_1 @ X14)) = (k1_xboole_0))
% 0.22/0.45          | ~ (r2_hidden @ k1_xboole_0 @ X14))),
% 0.22/0.45      inference('clc', [status(thm)], ['9', '10'])).
% 0.22/0.45  thf('12', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.45          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.45  thf(spc0_boole, axiom, (v1_xboole_0 @ np__0)).
% 0.22/0.45  thf('13', plain, ((v1_xboole_0 @ np__0)),
% 0.22/0.45      inference('cnf', [status(esa)], [spc0_boole])).
% 0.22/0.45  thf('14', plain, ((v1_xboole_0 @ np__0)),
% 0.22/0.45      inference('cnf', [status(esa)], [spc0_boole])).
% 0.22/0.45  thf(l13_xboole_0, axiom,
% 0.22/0.45    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.45  thf('15', plain,
% 0.22/0.45      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.22/0.45      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.45  thf('16', plain, (((np__0) = (k1_xboole_0))),
% 0.22/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.45  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.45      inference('demod', [status(thm)], ['13', '16'])).
% 0.22/0.45  thf(t4_yellow_1, axiom,
% 0.22/0.45    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.22/0.45  thf('18', plain,
% 0.22/0.45      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k2_yellow_1 @ (k9_setfam_1 @ X15)))),
% 0.22/0.45      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.22/0.45  thf('19', plain,
% 0.22/0.45      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.22/0.45      inference('demod', [status(thm)], ['12', '17', '18'])).
% 0.22/0.45  thf('20', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.45      inference('demod', [status(thm)], ['0', '19'])).
% 0.22/0.45  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
