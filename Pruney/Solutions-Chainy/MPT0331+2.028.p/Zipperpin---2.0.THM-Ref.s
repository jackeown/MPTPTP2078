%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n6LSphjqQg

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:07 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  423 ( 592 expanded)
%              Number of equality atoms :   42 (  58 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X17 @ X19 ) @ X20 )
        = ( k2_tarski @ X17 @ X19 ) )
      | ( r2_hidden @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k2_tarski @ X1 @ X0 ) )
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
       != ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
       != ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
       != ( k4_xboole_0 @ X2 @ X2 ) )
      | ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
       != ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['7','25'])).

thf('27',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n6LSphjqQg
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:30:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.74/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.97  % Solved by: fo/fo7.sh
% 0.74/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.97  % done 1152 iterations in 0.556s
% 0.74/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.97  % SZS output start Refutation
% 0.74/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.74/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.97  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.97  thf(t144_zfmisc_1, conjecture,
% 0.74/0.97    (![A:$i,B:$i,C:$i]:
% 0.74/0.97     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.74/0.97          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.74/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.74/0.97        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.74/0.97             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.74/0.97    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.74/0.97  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf(t72_zfmisc_1, axiom,
% 0.74/0.97    (![A:$i,B:$i,C:$i]:
% 0.74/0.97     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.74/0.97       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.74/0.97  thf('1', plain,
% 0.74/0.97      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.74/0.97         (((k4_xboole_0 @ (k2_tarski @ X17 @ X19) @ X20)
% 0.74/0.97            = (k2_tarski @ X17 @ X19))
% 0.74/0.97          | (r2_hidden @ X19 @ X20)
% 0.74/0.97          | (r2_hidden @ X17 @ X20))),
% 0.74/0.97      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.74/0.97  thf(t39_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.97  thf('2', plain,
% 0.74/0.97      (![X4 : $i, X5 : $i]:
% 0.74/0.97         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.74/0.97           = (k2_xboole_0 @ X4 @ X5))),
% 0.74/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.97  thf(t40_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.74/0.97  thf('3', plain,
% 0.74/0.97      (![X6 : $i, X7 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.74/0.97           = (k4_xboole_0 @ X6 @ X7))),
% 0.74/0.97      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.97  thf('4', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.74/0.97           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.74/0.97      inference('sup+', [status(thm)], ['2', '3'])).
% 0.74/0.97  thf('5', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.97         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) @ 
% 0.74/0.97            (k2_tarski @ X1 @ X0))
% 0.74/0.97            = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))
% 0.74/0.97          | (r2_hidden @ X1 @ X2)
% 0.74/0.97          | (r2_hidden @ X0 @ X2))),
% 0.74/0.97      inference('sup+', [status(thm)], ['1', '4'])).
% 0.74/0.97  thf('6', plain,
% 0.74/0.97      (![X6 : $i, X7 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.74/0.97           = (k4_xboole_0 @ X6 @ X7))),
% 0.74/0.97      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.97  thf('7', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.97         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0))
% 0.74/0.97            = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))
% 0.74/0.97          | (r2_hidden @ X1 @ X2)
% 0.74/0.97          | (r2_hidden @ X0 @ X2))),
% 0.74/0.97      inference('demod', [status(thm)], ['5', '6'])).
% 0.74/0.97  thf(t48_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.74/0.97  thf('8', plain,
% 0.74/0.97      (![X10 : $i, X11 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.74/0.97           = (k3_xboole_0 @ X10 @ X11))),
% 0.74/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/0.97  thf(t36_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.74/0.97  thf('9', plain,
% 0.74/0.97      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.74/0.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/0.97  thf(t45_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( r1_tarski @ A @ B ) =>
% 0.74/0.97       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.74/0.97  thf('10', plain,
% 0.74/0.97      (![X8 : $i, X9 : $i]:
% 0.74/0.97         (((X9) = (k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))
% 0.74/0.97          | ~ (r1_tarski @ X8 @ X9))),
% 0.74/0.97      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.74/0.97  thf('11', plain,
% 0.74/0.97      (![X4 : $i, X5 : $i]:
% 0.74/0.97         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.74/0.97           = (k2_xboole_0 @ X4 @ X5))),
% 0.74/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.97  thf('12', plain,
% 0.74/0.97      (![X8 : $i, X9 : $i]:
% 0.74/0.97         (((X9) = (k2_xboole_0 @ X8 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.74/0.97      inference('demod', [status(thm)], ['10', '11'])).
% 0.74/0.97  thf('13', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.74/0.97      inference('sup-', [status(thm)], ['9', '12'])).
% 0.74/0.97  thf('14', plain,
% 0.74/0.97      (![X6 : $i, X7 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.74/0.97           = (k4_xboole_0 @ X6 @ X7))),
% 0.74/0.97      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.97  thf('15', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X0 @ X0)
% 0.74/0.97           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.74/0.97      inference('sup+', [status(thm)], ['13', '14'])).
% 0.74/0.97  thf('16', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X1 @ X1)
% 0.74/0.97           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.74/0.97      inference('sup+', [status(thm)], ['8', '15'])).
% 0.74/0.97  thf(t49_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i,C:$i]:
% 0.74/0.97     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.74/0.97       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.74/0.97  thf('17', plain,
% 0.74/0.97      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.74/0.97         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.74/0.97           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 0.74/0.97      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.74/0.97  thf('18', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X0 @ X0)
% 0.74/0.97           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.74/0.97      inference('sup+', [status(thm)], ['13', '14'])).
% 0.74/0.97  thf(t32_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.74/0.97       ( ( A ) = ( B ) ) ))).
% 0.74/0.97  thf('19', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         (((X1) = (X0)) | ((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X0 @ X1)))),
% 0.74/0.97      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.74/0.97  thf('20', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         (((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.74/0.97            != (k4_xboole_0 @ X0 @ X0))
% 0.74/0.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.74/0.97      inference('sup-', [status(thm)], ['18', '19'])).
% 0.74/0.97  thf('21', plain,
% 0.74/0.97      (![X10 : $i, X11 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.74/0.97           = (k3_xboole_0 @ X10 @ X11))),
% 0.74/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/0.97  thf('22', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         (((k3_xboole_0 @ X0 @ X1) != (k4_xboole_0 @ X0 @ X0))
% 0.74/0.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.74/0.97      inference('demod', [status(thm)], ['20', '21'])).
% 0.74/0.97  thf('23', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.97         (((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 0.74/0.97            != (k4_xboole_0 @ X2 @ X2))
% 0.74/0.97          | ((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.74/0.97      inference('sup-', [status(thm)], ['17', '22'])).
% 0.74/0.97  thf('24', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         (((k4_xboole_0 @ X0 @ X0) != (k4_xboole_0 @ X0 @ X0))
% 0.74/0.97          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.74/0.97      inference('sup-', [status(thm)], ['16', '23'])).
% 0.74/0.97  thf('25', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.74/0.97      inference('simplify', [status(thm)], ['24'])).
% 0.74/0.97  thf('26', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.97         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2))
% 0.74/0.97          | (r2_hidden @ X1 @ X2)
% 0.74/0.97          | (r2_hidden @ X0 @ X2))),
% 0.74/0.97      inference('demod', [status(thm)], ['7', '25'])).
% 0.74/0.97  thf('27', plain,
% 0.74/0.97      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('28', plain,
% 0.74/0.97      ((((sk_C) != (sk_C))
% 0.74/0.97        | (r2_hidden @ sk_B @ sk_C)
% 0.74/0.97        | (r2_hidden @ sk_A @ sk_C))),
% 0.74/0.97      inference('sup-', [status(thm)], ['26', '27'])).
% 0.74/0.97  thf('29', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.74/0.97      inference('simplify', [status(thm)], ['28'])).
% 0.74/0.97  thf('30', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('31', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.74/0.97      inference('clc', [status(thm)], ['29', '30'])).
% 0.74/0.97  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.74/0.97  
% 0.74/0.97  % SZS output end Refutation
% 0.74/0.97  
% 0.81/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
