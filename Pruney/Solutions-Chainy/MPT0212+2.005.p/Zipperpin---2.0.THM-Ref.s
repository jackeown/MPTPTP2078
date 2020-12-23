%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ou7Wpod9Ts

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  78 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  380 ( 558 expanded)
%              Number of equality atoms :   54 (  83 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('0',plain,(
    ! [X52: $i,X55: $i] :
      ( ( X55
        = ( k1_zfmisc_1 @ X52 ) )
      | ( r1_tarski @ ( sk_C_1 @ X55 @ X52 ) @ X52 )
      | ( r2_hidden @ ( sk_C_1 @ X55 @ X52 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t1_zfmisc_1,conjecture,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t1_zfmisc_1])).

thf('8',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X52: $i,X55: $i] :
      ( ( X55
        = ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ ( sk_C_1 @ X55 @ X52 ) @ X52 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X55 @ X52 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('32',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','29','30','32'])).

thf('34',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ou7Wpod9Ts
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 64 iterations in 0.037s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(d1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X52 : $i, X55 : $i]:
% 0.20/0.49         (((X55) = (k1_zfmisc_1 @ X52))
% 0.20/0.49          | (r1_tarski @ (sk_C_1 @ X55 @ X52) @ X52)
% 0.20/0.49          | (r2_hidden @ (sk_C_1 @ X55 @ X52) @ X55))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.49  thf(t3_xboole_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X11 : $i]:
% 0.20/0.49         (((X11) = (k1_xboole_0)) | ~ (r1_tarski @ X11 @ k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.49          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.49          | ((sk_C_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(d1_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X21 @ X20)
% 0.20/0.49          | ((X21) = (X18))
% 0.20/0.49          | ((X20) != (k1_tarski @ X18)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X18 : $i, X21 : $i]:
% 0.20/0.49         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.49          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.49          | ((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) != (k1_xboole_0))
% 0.20/0.49          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.49          | ((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('eq_fact', [status(thm)], ['5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.49        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.49  thf(t1_zfmisc_1, conjecture,
% 0.20/0.49    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.20/0.49  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X52 : $i, X55 : $i]:
% 0.20/0.49         (((X55) = (k1_zfmisc_1 @ X52))
% 0.20/0.49          | ~ (r1_tarski @ (sk_C_1 @ X55 @ X52) @ X52)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C_1 @ X55 @ X52) @ X55))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.49        | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.20/0.49             (k1_tarski @ k1_xboole_0))
% 0.20/0.49        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.49           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.49           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(t5_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('16', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.49  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf(t98_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ X16 @ X17)
% 0.20/0.49           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.20/0.49           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['12', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf(t16_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.49       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.49           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.49           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf(t22_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) = (X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '25'])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         (((X19) != (X18))
% 0.20/0.49          | (r2_hidden @ X19 @ X20)
% 0.20/0.49          | ((X20) != (k1_tarski @ X18)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('32', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.20/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.49  thf('33', plain, (((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '29', '30', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
