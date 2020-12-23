%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0wn3yNe8au

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 219 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t9_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_setfam_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['8','13'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0wn3yNe8au
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:16:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 21 iterations in 0.012s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(t9_setfam_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( r2_hidden @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.22/0.48       ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( ( r2_hidden @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.22/0.48          ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t9_setfam_1])).
% 0.22/0.48  thf('0', plain, (~ (r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t4_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i]:
% 0.22/0.48         ((r1_tarski @ (k1_setfam_1 @ X10) @ X11) | ~ (r2_hidden @ X11 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.22/0.48  thf('3', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d7_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.48  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(t100_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.48           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf(t2_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.48           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf(t3_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.48  thf('12', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.48  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['8', '13'])).
% 0.22/0.48  thf(t106_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.22/0.48       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         ((r1_xboole_0 @ X5 @ X7)
% 0.22/0.48          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | (r1_xboole_0 @ X0 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf('17', plain, ((r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ sk_C)),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '16'])).
% 0.22/0.48  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
