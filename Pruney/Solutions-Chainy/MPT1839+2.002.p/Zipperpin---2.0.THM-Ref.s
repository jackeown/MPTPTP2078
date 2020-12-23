%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zGqpJn9doM

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:22 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   39 (  57 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  202 ( 358 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( v1_zfmisc_1 @ X40 )
      | ( X41 = X40 )
      | ~ ( r1_tarski @ X41 @ X40 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('21',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zGqpJn9doM
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:50:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 2133 iterations in 0.713s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.99/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.99/1.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.99/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.17  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(t2_tex_2, conjecture,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.99/1.17           ( r1_tarski @ A @ B ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.17    (~( ![A:$i]:
% 0.99/1.17        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.99/1.17          ( ![B:$i]:
% 0.99/1.17            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.99/1.17              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.99/1.17  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(commutativity_k2_tarski, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.99/1.17  thf('1', plain,
% 0.99/1.17      (![X27 : $i, X28 : $i]:
% 0.99/1.17         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.99/1.17  thf(t12_setfam_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.99/1.17  thf('2', plain,
% 0.99/1.17      (![X38 : $i, X39 : $i]:
% 0.99/1.17         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.99/1.17      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.99/1.17  thf('3', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('sup+', [status(thm)], ['1', '2'])).
% 0.99/1.17  thf('4', plain,
% 0.99/1.17      (![X38 : $i, X39 : $i]:
% 0.99/1.17         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.99/1.17      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('sup+', [status(thm)], ['3', '4'])).
% 0.99/1.17  thf(t48_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.99/1.17  thf('6', plain,
% 0.99/1.17      (![X25 : $i, X26 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.99/1.17           = (k3_xboole_0 @ X25 @ X26))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf(t36_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.99/1.17  thf('7', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i]: (r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X22)),
% 0.99/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.99/1.17      inference('sup+', [status(thm)], ['6', '7'])).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.99/1.17      inference('sup+', [status(thm)], ['5', '8'])).
% 0.99/1.17  thf(t1_tex_2, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.99/1.17           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.99/1.17  thf('10', plain,
% 0.99/1.17      (![X40 : $i, X41 : $i]:
% 0.99/1.17         ((v1_xboole_0 @ X40)
% 0.99/1.17          | ~ (v1_zfmisc_1 @ X40)
% 0.99/1.17          | ((X41) = (X40))
% 0.99/1.17          | ~ (r1_tarski @ X41 @ X40)
% 0.99/1.17          | (v1_xboole_0 @ X41))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.99/1.17  thf('11', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.99/1.17          | ((k3_xboole_0 @ X1 @ X0) = (X0))
% 0.99/1.17          | ~ (v1_zfmisc_1 @ X0)
% 0.99/1.17          | (v1_xboole_0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['9', '10'])).
% 0.99/1.17  thf('12', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('13', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('sup+', [status(thm)], ['3', '4'])).
% 0.99/1.17  thf('14', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['12', '13'])).
% 0.99/1.17  thf('15', plain,
% 0.99/1.17      (((v1_xboole_0 @ sk_A)
% 0.99/1.17        | ~ (v1_zfmisc_1 @ sk_A)
% 0.99/1.17        | ((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['11', '14'])).
% 0.99/1.17  thf('16', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['15', '16'])).
% 0.99/1.17  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('19', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))),
% 0.99/1.17      inference('clc', [status(thm)], ['17', '18'])).
% 0.99/1.17  thf('20', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.99/1.17      inference('sup+', [status(thm)], ['6', '7'])).
% 0.99/1.17  thf('21', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.99/1.17      inference('sup+', [status(thm)], ['19', '20'])).
% 0.99/1.17  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 0.99/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
