%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4uzocivM1N

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  219 ( 280 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X18 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) @ X8 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','14'])).

thf('16',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4uzocivM1N
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 38 iterations in 0.020s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(t48_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.47       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.47          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.20/0.47  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t38_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.20/0.47         ((r1_tarski @ (k2_tarski @ X18 @ X20) @ X21)
% 0.20/0.47          | ~ (r2_hidden @ X20 @ X21)
% 0.20/0.47          | ~ (r2_hidden @ X18 @ X21))),
% 0.20/0.47      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.47          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.47  thf(t45_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((X1) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.20/0.47          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.20/0.47  thf(t90_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         (r1_xboole_0 @ (k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) @ X8)),
% 0.20/0.47      inference('cnf', [status(esa)], [t90_xboole_1])).
% 0.20/0.47  thf(t47_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3))
% 0.20/0.47           = (k4_xboole_0 @ X2 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t83_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.47           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf(t98_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ X9 @ X10)
% 0.20/0.47           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.47           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ X9 @ X10)
% 0.20/0.47           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.47           = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((X1) = (k2_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['5', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (((sk_B) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
