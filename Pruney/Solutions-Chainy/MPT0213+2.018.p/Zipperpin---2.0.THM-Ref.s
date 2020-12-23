%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BrOZHbAc9B

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:44 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 150 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  338 (1555 expanded)
%              Number of equality atoms :   24 ( 104 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k3_tarski @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X6 ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('2',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k3_tarski @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X6 ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('9',plain,(
    ! [X6: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X11 )
      | ~ ( r2_hidden @ X11 @ X6 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_xboole_0
      = ( k3_tarski @ k1_xboole_0 ) )
    | ( ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf(t2_zfmisc_1,conjecture,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t2_zfmisc_1])).

thf('15',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_tarski @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('18',plain,
    ( ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k3_tarski @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('22',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['23','31'])).

thf('33',plain,(
    $false ),
    inference('sup-',[status(thm)],['20','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BrOZHbAc9B
% 0.16/0.38  % Computer   : n024.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 18:05:06 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 214 iterations in 0.111s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.42/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.42/0.61  thf('0', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.42/0.61  thf(d4_tarski, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.42/0.61       ( ![C:$i]:
% 0.42/0.61         ( ( r2_hidden @ C @ B ) <=>
% 0.42/0.61           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X6 : $i, X10 : $i]:
% 0.42/0.61         (((X10) = (k3_tarski @ X6))
% 0.42/0.61          | (r2_hidden @ (sk_D @ X10 @ X6) @ X6)
% 0.42/0.61          | (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_tarski])).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X6 : $i, X10 : $i]:
% 0.42/0.61         (((X10) = (k3_tarski @ X6))
% 0.42/0.61          | (r2_hidden @ (sk_D @ X10 @ X6) @ X6)
% 0.42/0.61          | (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_tarski])).
% 0.42/0.61  thf(t3_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.42/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.42/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.42/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.42/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.42/0.61          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.42/0.61          | ((X1) = (k3_tarski @ X0))
% 0.42/0.61          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.42/0.61          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.42/0.61          | ((X1) = (k3_tarski @ X0))
% 0.42/0.61          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.42/0.61          | ((X1) = (k3_tarski @ X0))
% 0.42/0.61          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r1_xboole_0 @ X0 @ X0)
% 0.42/0.61          | ((X1) = (k3_tarski @ X0))
% 0.42/0.61          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 0.42/0.61      inference('simplify', [status(thm)], ['5'])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.42/0.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '6'])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.42/0.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '6'])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X6 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         (((X10) = (k3_tarski @ X6))
% 0.42/0.61          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X11)
% 0.42/0.61          | ~ (r2_hidden @ X11 @ X6)
% 0.42/0.61          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_tarski])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((X0) = (k3_tarski @ k1_xboole_0))
% 0.42/0.61          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.42/0.61          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.42/0.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.42/0.61          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.42/0.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.42/0.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '6'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((X0) = (k3_tarski @ k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.42/0.61      inference('clc', [status(thm)], ['11', '12'])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      ((((k1_xboole_0) = (k3_tarski @ k1_xboole_0))
% 0.42/0.61        | ((sk_C_1 @ k1_xboole_0 @ k1_xboole_0) = (k3_tarski @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['7', '13'])).
% 0.42/0.61  thf(t2_zfmisc_1, conjecture, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (( k3_tarski @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t2_zfmisc_1])).
% 0.42/0.61  thf('15', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (((sk_C_1 @ k1_xboole_0 @ k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.42/0.61          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '6'])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)
% 0.42/0.61        | ((k1_xboole_0) = (k3_tarski @ k1_xboole_0)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['16', '17'])).
% 0.42/0.61  thf('19', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('20', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.42/0.61  thf('21', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.42/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.42/0.61          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.42/0.61          | ~ (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.61  thf('24', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.42/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.42/0.61          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((r1_xboole_0 @ X0 @ X1)
% 0.42/0.61          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.42/0.61          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r1_xboole_0 @ X0 @ X1)
% 0.42/0.61          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.42/0.61          | (r1_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['25', '28'])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.42/0.61  thf('31', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.42/0.61      inference('sup-', [status(thm)], ['24', '30'])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X0 : $i]: ~ (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0)),
% 0.42/0.61      inference('demod', [status(thm)], ['23', '31'])).
% 0.42/0.61  thf('33', plain, ($false), inference('sup-', [status(thm)], ['20', '32'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
