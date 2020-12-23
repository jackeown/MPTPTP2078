%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qTjXrxWlQU

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:13 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   47 (  49 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  186 ( 199 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xcmplx_0_type,type,(
    v1_xcmplx_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xreal_0_type,type,(
    v1_xreal_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xxreal_0_type,type,(
    v1_xxreal_0: $i > $o )).

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
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A_1 ) )
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

thf(rc4_xreal_0,axiom,(
    ? [A: $i] :
      ( ( v1_xreal_0 @ A )
      & ( v1_xxreal_0 @ A )
      & ( v1_xcmplx_0 @ A )
      & ( v1_xboole_0 @ A ) ) )).

thf('13',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc4_xreal_0])).

thf('14',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc4_xreal_0])).

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
    sk_A = k1_xboole_0 ),
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
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qTjXrxWlQU
% 0.17/0.38  % Computer   : n024.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 16:30:06 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 32 iterations in 0.018s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.51  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.25/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.51  thf(v1_xcmplx_0_type, type, v1_xcmplx_0: $i > $o).
% 0.25/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.51  thf(v1_xreal_0_type, type, v1_xreal_0: $i > $o).
% 0.25/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.51  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.25/0.51  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.25/0.51  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.25/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(v1_xxreal_0_type, type, v1_xxreal_0: $i > $o).
% 0.25/0.51  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.25/0.51  thf(t18_yellow_1, conjecture,
% 0.25/0.51    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.25/0.51  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A_1)) != (k1_xboole_0))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(d3_tarski, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.25/0.51  thf('1', plain,
% 0.25/0.51      (![X4 : $i, X6 : $i]:
% 0.25/0.51         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.25/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.51  thf(d1_xboole_0, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.25/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.25/0.51  thf('3', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.51  thf(d1_zfmisc_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.25/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.25/0.51  thf('4', plain,
% 0.25/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.51         (~ (r1_tarski @ X8 @ X9)
% 0.25/0.51          | (r2_hidden @ X8 @ X10)
% 0.25/0.51          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.25/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      (![X8 : $i, X9 : $i]:
% 0.25/0.51         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.25/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.25/0.51  thf(redefinition_k9_setfam_1, axiom,
% 0.25/0.51    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.25/0.51  thf('6', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.25/0.51      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.25/0.51  thf('7', plain,
% 0.25/0.51      (![X8 : $i, X9 : $i]:
% 0.25/0.51         ((r2_hidden @ X8 @ (k9_setfam_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.25/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.25/0.51  thf('8', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (v1_xboole_0 @ X1) | (r2_hidden @ X1 @ (k9_setfam_1 @ X0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['3', '7'])).
% 0.25/0.51  thf(t13_yellow_1, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.51       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.25/0.51         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.25/0.51  thf('9', plain,
% 0.25/0.51      (![X14 : $i]:
% 0.25/0.51         (~ (r2_hidden @ k1_xboole_0 @ X14)
% 0.25/0.51          | ((k3_yellow_0 @ (k2_yellow_1 @ X14)) = (k1_xboole_0))
% 0.25/0.51          | (v1_xboole_0 @ X14))),
% 0.25/0.51      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.25/0.51  thf('10', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.25/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.25/0.51  thf('11', plain,
% 0.25/0.51      (![X14 : $i]:
% 0.25/0.51         (((k3_yellow_0 @ (k2_yellow_1 @ X14)) = (k1_xboole_0))
% 0.25/0.51          | ~ (r2_hidden @ k1_xboole_0 @ X14))),
% 0.25/0.51      inference('clc', [status(thm)], ['9', '10'])).
% 0.25/0.51  thf('12', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.25/0.51          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['8', '11'])).
% 0.25/0.51  thf(rc4_xreal_0, axiom,
% 0.25/0.51    (?[A:$i]:
% 0.25/0.51     ( ( v1_xreal_0 @ A ) & ( v1_xxreal_0 @ A ) & ( v1_xcmplx_0 @ A ) & 
% 0.25/0.51       ( v1_xboole_0 @ A ) ))).
% 0.25/0.51  thf('13', plain, ((v1_xboole_0 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [rc4_xreal_0])).
% 0.25/0.51  thf('14', plain, ((v1_xboole_0 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [rc4_xreal_0])).
% 0.25/0.51  thf(l13_xboole_0, axiom,
% 0.25/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.51  thf('15', plain,
% 0.25/0.51      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.25/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.25/0.51  thf('16', plain, (((sk_A) = (k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.51  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.51      inference('demod', [status(thm)], ['13', '16'])).
% 0.25/0.51  thf(t4_yellow_1, axiom,
% 0.25/0.51    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.25/0.51  thf('18', plain,
% 0.25/0.51      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k2_yellow_1 @ (k9_setfam_1 @ X15)))),
% 0.25/0.51      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.25/0.51  thf('19', plain,
% 0.25/0.51      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.25/0.51      inference('demod', [status(thm)], ['12', '17', '18'])).
% 0.25/0.51  thf('20', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.25/0.51      inference('demod', [status(thm)], ['0', '19'])).
% 0.25/0.51  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
