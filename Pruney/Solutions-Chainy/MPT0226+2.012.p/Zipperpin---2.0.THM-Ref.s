%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sNIXIEy3ed

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  253 ( 288 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X36 ) @ X37 )
      | ( r2_hidden @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference('sup-',[status(thm)],['19','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sNIXIEy3ed
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:43:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 57 iterations in 0.027s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(d1_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf(l27_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X36 : $i, X37 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ (k1_tarski @ X36) @ X37) | (r2_hidden @ X36 @ X37))),
% 0.22/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.22/0.49  thf(t21_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49         ( k1_xboole_0 ) ) =>
% 0.22/0.49       ( ( A ) = ( B ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49            ( k1_xboole_0 ) ) =>
% 0.22/0.49          ( ( A ) = ( B ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49         = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t48_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.49           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.22/0.49         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(t4_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.22/0.49          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))
% 0.22/0.49          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.22/0.49          | ~ (r2_hidden @ X0 @ 
% 0.22/0.49               (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((v1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))
% 0.22/0.49        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.49  thf(d1_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X21 @ X20)
% 0.22/0.49          | ((X21) = (X18))
% 0.22/0.49          | ((X20) != (k1_tarski @ X18)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X18 : $i, X21 : $i]:
% 0.22/0.49         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (((v1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (sk_B_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.49  thf('12', plain, (((sk_A) != (sk_B_1))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      ((v1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf(t2_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.49  thf(t100_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X7 @ X8)
% 0.22/0.49           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf(t5_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('17', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.49  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (((X19) != (X18))
% 0.22/0.49          | (r2_hidden @ X19 @ X20)
% 0.22/0.49          | ((X20) != (k1_tarski @ X18)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('21', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.22/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf('23', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain, ($false), inference('sup-', [status(thm)], ['19', '23'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
