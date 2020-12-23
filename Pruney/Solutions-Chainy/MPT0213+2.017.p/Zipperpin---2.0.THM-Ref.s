%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OGibrhFVl6

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:44 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 248 expanded)
%              Number of leaves         :   13 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  355 (2464 expanded)
%              Number of equality atoms :   26 ( 122 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X12: $i] :
      ( ( X12
        = ( k3_tarski @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X8 ) @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X8 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('11',plain,(
    ! [X8: $i,X12: $i] :
      ( ( X12
        = ( k3_tarski @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X8 ) @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X8 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('18',plain,(
    ! [X8: $i,X12: $i,X13: $i] :
      ( ( X12
        = ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X8 ) @ X13 )
      | ~ ( r2_hidden @ X13 @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X8 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k3_tarski @ k1_xboole_0 ) )
    | ( ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf(t2_zfmisc_1,conjecture,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t2_zfmisc_1])).

thf('24',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_tarski @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('27',plain,
    ( ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k3_tarski @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['29','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OGibrhFVl6
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 268 iterations in 0.147s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.60  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.36/0.60  thf(t4_boole, axiom,
% 0.36/0.60    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t4_boole])).
% 0.36/0.60  thf(t79_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X6)),
% 0.36/0.60      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.36/0.60  thf('2', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.36/0.60      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.60  thf(t3_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.36/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X2 @ X0)
% 0.36/0.60          | ~ (r2_hidden @ X2 @ X3)
% 0.36/0.60          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r1_xboole_0 @ X1 @ X0)
% 0.36/0.60          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.36/0.60          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.36/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_xboole_0 @ X0 @ X1)
% 0.36/0.60          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.36/0.60          | (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['3', '6'])).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('simplify', [status(thm)], ['7'])).
% 0.36/0.60  thf('9', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.36/0.60      inference('sup-', [status(thm)], ['2', '8'])).
% 0.36/0.60  thf(d4_tarski, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.36/0.60       ( ![C:$i]:
% 0.36/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.60           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      (![X8 : $i, X12 : $i]:
% 0.36/0.60         (((X12) = (k3_tarski @ X8))
% 0.36/0.60          | (r2_hidden @ (sk_D @ X12 @ X8) @ X8)
% 0.36/0.60          | (r2_hidden @ (sk_C_1 @ X12 @ X8) @ X12))),
% 0.36/0.60      inference('cnf', [status(esa)], [d4_tarski])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (![X8 : $i, X12 : $i]:
% 0.36/0.60         (((X12) = (k3_tarski @ X8))
% 0.36/0.60          | (r2_hidden @ (sk_D @ X12 @ X8) @ X8)
% 0.36/0.60          | (r2_hidden @ (sk_C_1 @ X12 @ X8) @ X12))),
% 0.36/0.60      inference('cnf', [status(esa)], [d4_tarski])).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X2 @ X0)
% 0.36/0.60          | ~ (r2_hidden @ X2 @ X3)
% 0.36/0.60          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.36/0.60          | ((X1) = (k3_tarski @ X0))
% 0.36/0.60          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.36/0.60          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.36/0.60          | ((X1) = (k3_tarski @ X0))
% 0.36/0.60          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.36/0.60          | ((X1) = (k3_tarski @ X0))
% 0.36/0.60          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['10', '13'])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_xboole_0 @ X0 @ X0)
% 0.36/0.60          | ((X1) = (k3_tarski @ X0))
% 0.36/0.60          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 0.36/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.36/0.60          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['9', '15'])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.36/0.60          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['9', '15'])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X8 : $i, X12 : $i, X13 : $i]:
% 0.36/0.60         (((X12) = (k3_tarski @ X8))
% 0.36/0.60          | ~ (r2_hidden @ (sk_C_1 @ X12 @ X8) @ X13)
% 0.36/0.60          | ~ (r2_hidden @ X13 @ X8)
% 0.36/0.60          | ~ (r2_hidden @ (sk_C_1 @ X12 @ X8) @ X12))),
% 0.36/0.60      inference('cnf', [status(esa)], [d4_tarski])).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((X0) = (k3_tarski @ k1_xboole_0))
% 0.36/0.60          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.36/0.60          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.36/0.60          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.36/0.60          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.36/0.60          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.36/0.60          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['9', '15'])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((X0) = (k3_tarski @ k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.36/0.60      inference('clc', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      ((((k1_xboole_0) = (k3_tarski @ k1_xboole_0))
% 0.36/0.60        | ((sk_C_1 @ k1_xboole_0 @ k1_xboole_0) = (k3_tarski @ k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['16', '22'])).
% 0.36/0.60  thf(t2_zfmisc_1, conjecture, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (( k3_tarski @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t2_zfmisc_1])).
% 0.36/0.60  thf('24', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (((sk_C_1 @ k1_xboole_0 @ k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 0.36/0.60      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.36/0.60          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['9', '15'])).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)
% 0.36/0.60        | ((k1_xboole_0) = (k3_tarski @ k1_xboole_0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['25', '26'])).
% 0.36/0.60  thf('28', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('29', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.36/0.60      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.36/0.60  thf('30', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.36/0.60      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X2 @ X0)
% 0.36/0.60          | ~ (r2_hidden @ X2 @ X3)
% 0.36/0.60          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.60          | ~ (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.60  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.36/0.60      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (![X0 : $i]: ~ (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0)),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('35', plain, ($false), inference('sup-', [status(thm)], ['29', '34'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
