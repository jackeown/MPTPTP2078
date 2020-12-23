%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JlPPXvw7Sv

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  50 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  179 ( 312 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( v1_zfmisc_1 @ X6 )
      | ( X7 = X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JlPPXvw7Sv
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 24 iterations in 0.015s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.43  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.43  thf(t2_tex_2, conjecture,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.20/0.43       ( ![B:$i]:
% 0.20/0.43         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.20/0.43           ( r1_tarski @ A @ B ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i]:
% 0.20/0.43        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.20/0.43          ( ![B:$i]:
% 0.20/0.43            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.20/0.43              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.20/0.43  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(commutativity_k2_tarski, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.43  thf(t12_setfam_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X4 : $i, X5 : $i]:
% 0.20/0.43         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.20/0.43      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.43      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X4 : $i, X5 : $i]:
% 0.20/0.43         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.20/0.43      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.43      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.43  thf(t17_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.43      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.43  thf('7', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.43      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.43  thf(t1_tex_2, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.43       ( ![B:$i]:
% 0.20/0.43         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.43           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (![X6 : $i, X7 : $i]:
% 0.20/0.43         ((v1_xboole_0 @ X6)
% 0.20/0.43          | ~ (v1_zfmisc_1 @ X6)
% 0.20/0.43          | ((X7) = (X6))
% 0.20/0.43          | ~ (r1_tarski @ X7 @ X6)
% 0.20/0.43          | (v1_xboole_0 @ X7))),
% 0.20/0.43      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.43          | ((k3_xboole_0 @ X1 @ X0) = (X0))
% 0.20/0.43          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.43          | (v1_xboole_0 @ X0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.43  thf('10', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.43      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.43  thf('12', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.43      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.43  thf('13', plain,
% 0.20/0.43      (((v1_xboole_0 @ sk_A)
% 0.20/0.43        | ~ (v1_zfmisc_1 @ sk_A)
% 0.20/0.43        | ((k3_xboole_0 @ sk_B @ sk_A) = (sk_A)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.43  thf('14', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('15', plain,
% 0.20/0.43      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_B @ sk_A) = (sk_A)))),
% 0.20/0.43      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.43  thf('16', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('17', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.20/0.43      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.43  thf('18', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.43      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.43  thf('19', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.43      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.43  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
