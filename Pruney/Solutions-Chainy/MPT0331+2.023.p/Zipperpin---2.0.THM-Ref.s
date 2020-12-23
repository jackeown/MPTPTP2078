%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U6oj0OT4AF

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:06 EST 2020

% Result     : Theorem 44.10s
% Output     : Refutation 44.10s
% Verified   : 
% Statistics : Number of formulae       :   42 (  74 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  456 ( 949 expanded)
%              Number of equality atoms :   42 (  76 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) )
      | ( ( sk_D @ ( k2_tarski @ X1 @ X0 ) @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_D @ ( k2_tarski @ X1 @ X0 ) @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X2 ) @ X1 @ ( k2_tarski @ X0 @ X2 ) )
        = X2 )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X0 @ X2 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X2 ) @ X1 @ ( k2_tarski @ X0 @ X2 ) )
        = X2 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X1 )
      | ( ( k2_tarski @ X2 @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ X1 ) )
      | ( ( k2_tarski @ X2 @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ X1 ) )
      | ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U6oj0OT4AF
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 44.10/44.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 44.10/44.29  % Solved by: fo/fo7.sh
% 44.10/44.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.10/44.29  % done 17245 iterations in 43.836s
% 44.10/44.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 44.10/44.29  % SZS output start Refutation
% 44.10/44.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 44.10/44.29  thf(sk_C_type, type, sk_C: $i).
% 44.10/44.29  thf(sk_A_type, type, sk_A: $i).
% 44.10/44.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 44.10/44.29  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 44.10/44.29  thf(sk_B_type, type, sk_B: $i).
% 44.10/44.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 44.10/44.29  thf(t144_zfmisc_1, conjecture,
% 44.10/44.29    (![A:$i,B:$i,C:$i]:
% 44.10/44.29     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 44.10/44.29          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 44.10/44.29  thf(zf_stmt_0, negated_conjecture,
% 44.10/44.29    (~( ![A:$i,B:$i,C:$i]:
% 44.10/44.29        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 44.10/44.29             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 44.10/44.29    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 44.10/44.29  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 44.10/44.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.10/44.29  thf(d5_xboole_0, axiom,
% 44.10/44.29    (![A:$i,B:$i,C:$i]:
% 44.10/44.29     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 44.10/44.29       ( ![D:$i]:
% 44.10/44.29         ( ( r2_hidden @ D @ C ) <=>
% 44.10/44.29           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 44.10/44.29  thf('1', plain,
% 44.10/44.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 44.10/44.29         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 44.10/44.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 44.10/44.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 44.10/44.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 44.10/44.29  thf('2', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 44.10/44.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 44.10/44.29      inference('eq_fact', [status(thm)], ['1'])).
% 44.10/44.29  thf(d2_tarski, axiom,
% 44.10/44.29    (![A:$i,B:$i,C:$i]:
% 44.10/44.29     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 44.10/44.29       ( ![D:$i]:
% 44.10/44.29         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 44.10/44.29  thf('3', plain,
% 44.10/44.29      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 44.10/44.29         (~ (r2_hidden @ X12 @ X10)
% 44.10/44.29          | ((X12) = (X11))
% 44.10/44.29          | ((X12) = (X8))
% 44.10/44.29          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 44.10/44.29      inference('cnf', [status(esa)], [d2_tarski])).
% 44.10/44.29  thf('4', plain,
% 44.10/44.29      (![X8 : $i, X11 : $i, X12 : $i]:
% 44.10/44.29         (((X12) = (X8))
% 44.10/44.29          | ((X12) = (X11))
% 44.10/44.29          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 44.10/44.29      inference('simplify', [status(thm)], ['3'])).
% 44.10/44.29  thf('5', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.10/44.29         (((k2_tarski @ X1 @ X0) = (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))
% 44.10/44.29          | ((sk_D @ (k2_tarski @ X1 @ X0) @ X2 @ (k2_tarski @ X1 @ X0)) = (X1))
% 44.10/44.29          | ((sk_D @ (k2_tarski @ X1 @ X0) @ X2 @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 44.10/44.29      inference('sup-', [status(thm)], ['2', '4'])).
% 44.10/44.29  thf('6', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 44.10/44.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 44.10/44.29      inference('eq_fact', [status(thm)], ['1'])).
% 44.10/44.29  thf('7', plain,
% 44.10/44.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 44.10/44.29         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 44.10/44.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 44.10/44.29          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 44.10/44.29          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 44.10/44.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 44.10/44.29  thf('8', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 44.10/44.29          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 44.10/44.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 44.10/44.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 44.10/44.29      inference('sup-', [status(thm)], ['6', '7'])).
% 44.10/44.29  thf('9', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 44.10/44.29          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 44.10/44.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 44.10/44.29      inference('simplify', [status(thm)], ['8'])).
% 44.10/44.29  thf('10', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 44.10/44.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 44.10/44.29      inference('eq_fact', [status(thm)], ['1'])).
% 44.10/44.29  thf('11', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 44.10/44.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 44.10/44.29      inference('clc', [status(thm)], ['9', '10'])).
% 44.10/44.29  thf('12', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.10/44.29         ((r2_hidden @ X0 @ X1)
% 44.10/44.29          | ((sk_D @ (k2_tarski @ X0 @ X2) @ X1 @ (k2_tarski @ X0 @ X2)) = (X2))
% 44.10/44.29          | ((k2_tarski @ X0 @ X2) = (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1))
% 44.10/44.29          | ((k2_tarski @ X0 @ X2) = (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)))),
% 44.10/44.29      inference('sup+', [status(thm)], ['5', '11'])).
% 44.10/44.29  thf('13', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.10/44.29         (((k2_tarski @ X0 @ X2) = (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1))
% 44.10/44.29          | ((sk_D @ (k2_tarski @ X0 @ X2) @ X1 @ (k2_tarski @ X0 @ X2)) = (X2))
% 44.10/44.29          | (r2_hidden @ X0 @ X1))),
% 44.10/44.29      inference('simplify', [status(thm)], ['12'])).
% 44.10/44.29  thf('14', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 44.10/44.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 44.10/44.29      inference('clc', [status(thm)], ['9', '10'])).
% 44.10/44.29  thf('15', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.10/44.29         ((r2_hidden @ X0 @ X1)
% 44.10/44.29          | (r2_hidden @ X2 @ X1)
% 44.10/44.29          | ((k2_tarski @ X2 @ X0) = (k4_xboole_0 @ (k2_tarski @ X2 @ X0) @ X1))
% 44.10/44.29          | ((k2_tarski @ X2 @ X0) = (k4_xboole_0 @ (k2_tarski @ X2 @ X0) @ X1)))),
% 44.10/44.29      inference('sup+', [status(thm)], ['13', '14'])).
% 44.10/44.29  thf('16', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.10/44.29         (((k2_tarski @ X2 @ X0) = (k4_xboole_0 @ (k2_tarski @ X2 @ X0) @ X1))
% 44.10/44.29          | (r2_hidden @ X2 @ X1)
% 44.10/44.29          | (r2_hidden @ X0 @ X1))),
% 44.10/44.29      inference('simplify', [status(thm)], ['15'])).
% 44.10/44.29  thf('17', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 44.10/44.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 44.10/44.29      inference('eq_fact', [status(thm)], ['1'])).
% 44.10/44.29  thf('18', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 44.10/44.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 44.10/44.29      inference('clc', [status(thm)], ['9', '10'])).
% 44.10/44.29  thf('19', plain,
% 44.10/44.29      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 44.10/44.29         (~ (r2_hidden @ X4 @ X3)
% 44.10/44.29          | ~ (r2_hidden @ X4 @ X2)
% 44.10/44.29          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 44.10/44.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 44.10/44.29  thf('20', plain,
% 44.10/44.29      (![X1 : $i, X2 : $i, X4 : $i]:
% 44.10/44.29         (~ (r2_hidden @ X4 @ X2)
% 44.10/44.29          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 44.10/44.29      inference('simplify', [status(thm)], ['19'])).
% 44.10/44.29  thf('21', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.10/44.29         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 44.10/44.29          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 44.10/44.29      inference('sup-', [status(thm)], ['18', '20'])).
% 44.10/44.29  thf('22', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 44.10/44.29          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.10/44.29      inference('sup-', [status(thm)], ['17', '21'])).
% 44.10/44.29  thf('23', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i]:
% 44.10/44.29         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.10/44.29      inference('simplify', [status(thm)], ['22'])).
% 44.10/44.29  thf('24', plain,
% 44.10/44.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.10/44.29         (((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 44.10/44.29          | (r2_hidden @ X0 @ X2)
% 44.10/44.29          | (r2_hidden @ X1 @ X2))),
% 44.10/44.29      inference('sup+', [status(thm)], ['16', '23'])).
% 44.10/44.29  thf('25', plain,
% 44.10/44.29      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 44.10/44.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.10/44.29  thf('26', plain,
% 44.10/44.29      ((((sk_C) != (sk_C))
% 44.10/44.29        | (r2_hidden @ sk_A @ sk_C)
% 44.10/44.29        | (r2_hidden @ sk_B @ sk_C))),
% 44.10/44.29      inference('sup-', [status(thm)], ['24', '25'])).
% 44.10/44.29  thf('27', plain, (((r2_hidden @ sk_B @ sk_C) | (r2_hidden @ sk_A @ sk_C))),
% 44.10/44.29      inference('simplify', [status(thm)], ['26'])).
% 44.10/44.29  thf('28', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 44.10/44.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.10/44.29  thf('29', plain, ((r2_hidden @ sk_A @ sk_C)),
% 44.10/44.29      inference('clc', [status(thm)], ['27', '28'])).
% 44.10/44.29  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 44.10/44.29  
% 44.10/44.29  % SZS output end Refutation
% 44.10/44.29  
% 44.10/44.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
