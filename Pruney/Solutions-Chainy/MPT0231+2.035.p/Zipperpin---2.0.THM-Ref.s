%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MOJTgldmDG

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:32 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  230 ( 265 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) )
    = ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_C ) )
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_C ) ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_C )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','12'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k1_tarski @ X18 ) @ ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('19',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MOJTgldmDG
% 0.16/0.37  % Computer   : n016.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:51:34 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 107 iterations in 0.050s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(t26_zfmisc_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.35/0.53       ( ( A ) = ( C ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.53        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.35/0.53          ( ( A ) = ( C ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t12_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))
% 0.35/0.53         = (k1_tarski @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf(t40_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X8 : $i, X9 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.35/0.53           = (k4_xboole_0 @ X8 @ X9))),
% 0.35/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_C))
% 0.35/0.53         = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['2', '3'])).
% 0.35/0.53  thf(t39_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]:
% 0.35/0.53         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.35/0.53           = (k2_xboole_0 @ X6 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_C) @ 
% 0.35/0.53         (k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_C)))
% 0.35/0.53         = (k2_xboole_0 @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]:
% 0.35/0.53         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.35/0.53           = (k2_xboole_0 @ X6 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.35/0.53  thf(t1_boole, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.53  thf('8', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.53  thf(t7_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.35/0.53  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.35/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.35/0.53  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (((k1_tarski @ sk_C)
% 0.35/0.53         = (k2_xboole_0 @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['6', '7', '12'])).
% 0.35/0.53  thf(t12_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i]:
% 0.35/0.53         (r1_tarski @ (k1_tarski @ X18) @ (k2_tarski @ X18 @ X19))),
% 0.35/0.53      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.35/0.53  thf(t10_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (r1_tarski @ (k1_tarski @ X1) @ 
% 0.35/0.53          (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.53  thf('17', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.35/0.53      inference('sup+', [status(thm)], ['13', '16'])).
% 0.35/0.53  thf(t6_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.35/0.53       ( ( A ) = ( B ) ) ))).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]:
% 0.35/0.53         (((X21) = (X20))
% 0.35/0.53          | ~ (r1_tarski @ (k1_tarski @ X21) @ (k1_tarski @ X20)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.35/0.53  thf('19', plain, (((sk_A) = (sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.53  thf('20', plain, (((sk_A) != (sk_C))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('21', plain, ($false),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
