%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SWdtZLMTMz

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:42 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   49 (  82 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  324 ( 588 expanded)
%              Number of equality atoms :   39 (  71 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X42 @ X41 ) @ X41 )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( X23 = X20 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X38 ) )
       != X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X21 != X20 )
      | ( r2_hidden @ X21 @ X22 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X20: $i] :
      ( r2_hidden @ X20 @ ( k1_tarski @ X20 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('16',plain,(
    ! [X20: $i] :
      ( r2_hidden @ X20 @ ( k1_tarski @ X20 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( r1_tarski @ X43 @ X45 )
      | ( r1_tarski @ ( k1_setfam_1 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ X42 @ ( sk_C_2 @ X42 @ X41 ) )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['10','12'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SWdtZLMTMz
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.71  % Solved by: fo/fo7.sh
% 0.45/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.71  % done 378 iterations in 0.258s
% 0.45/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.71  % SZS output start Refutation
% 0.45/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.71  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.45/0.71  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.71  thf(t11_setfam_1, conjecture,
% 0.45/0.71    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.45/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.71    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.45/0.71    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.45/0.71  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(t6_setfam_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.45/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.45/0.71  thf('1', plain,
% 0.45/0.71      (![X41 : $i, X42 : $i]:
% 0.45/0.71         (((X41) = (k1_xboole_0))
% 0.45/0.71          | (r2_hidden @ (sk_C_2 @ X42 @ X41) @ X41)
% 0.45/0.71          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.45/0.71  thf(d1_tarski, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.71  thf('2', plain,
% 0.45/0.71      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X23 @ X22)
% 0.45/0.71          | ((X23) = (X20))
% 0.45/0.71          | ((X22) != (k1_tarski @ X20)))),
% 0.45/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.71  thf('3', plain,
% 0.45/0.71      (![X20 : $i, X23 : $i]:
% 0.45/0.71         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.45/0.71      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.71  thf('4', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.45/0.71          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.71          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['1', '3'])).
% 0.45/0.71  thf(d10_xboole_0, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.71  thf('5', plain,
% 0.45/0.71      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.45/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.71  thf('6', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.71      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.71  thf(l32_xboole_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.71  thf('7', plain,
% 0.45/0.71      (![X5 : $i, X7 : $i]:
% 0.45/0.71         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.45/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.71  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.71  thf(t65_zfmisc_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.45/0.71       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.45/0.71  thf('9', plain,
% 0.45/0.71      (![X38 : $i, X39 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X38 @ X39)
% 0.45/0.71          | ((k4_xboole_0 @ X39 @ (k1_tarski @ X38)) != (X39)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.45/0.71  thf('10', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.45/0.71          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.71  thf('11', plain,
% 0.45/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.71         (((X21) != (X20))
% 0.45/0.71          | (r2_hidden @ X21 @ X22)
% 0.45/0.71          | ((X22) != (k1_tarski @ X20)))),
% 0.45/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.71  thf('12', plain, (![X20 : $i]: (r2_hidden @ X20 @ (k1_tarski @ X20))),
% 0.45/0.71      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.71  thf('13', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.45/0.71      inference('demod', [status(thm)], ['10', '12'])).
% 0.45/0.71  thf('14', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.45/0.71          | (r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.45/0.71      inference('clc', [status(thm)], ['4', '13'])).
% 0.45/0.71  thf('15', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.71      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.71  thf('16', plain, (![X20 : $i]: (r2_hidden @ X20 @ (k1_tarski @ X20))),
% 0.45/0.71      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.71  thf(t8_setfam_1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.45/0.71       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.45/0.71  thf('17', plain,
% 0.45/0.71      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X43 @ X44)
% 0.45/0.71          | ~ (r1_tarski @ X43 @ X45)
% 0.45/0.71          | (r1_tarski @ (k1_setfam_1 @ X44) @ X45))),
% 0.45/0.71      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.45/0.71  thf('18', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.45/0.71          | ~ (r1_tarski @ X0 @ X1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.71  thf('19', plain,
% 0.45/0.71      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.45/0.71      inference('sup-', [status(thm)], ['15', '18'])).
% 0.45/0.71  thf('20', plain,
% 0.45/0.71      (![X2 : $i, X4 : $i]:
% 0.45/0.71         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.71  thf('21', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.45/0.71          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.71  thf('22', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.45/0.71          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['14', '21'])).
% 0.45/0.71  thf('23', plain,
% 0.45/0.71      (![X41 : $i, X42 : $i]:
% 0.45/0.71         (((X41) = (k1_xboole_0))
% 0.45/0.71          | ~ (r1_tarski @ X42 @ (sk_C_2 @ X42 @ X41))
% 0.45/0.71          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.45/0.71  thf('24', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (r1_tarski @ X0 @ X0)
% 0.45/0.71          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.45/0.71          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.45/0.71          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.71  thf('25', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.71      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.71  thf('26', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.45/0.71          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.45/0.71          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.71      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.71  thf('27', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.45/0.71          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.71  thf('28', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.71          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.45/0.71      inference('clc', [status(thm)], ['26', '27'])).
% 0.45/0.71  thf('29', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.45/0.71      inference('demod', [status(thm)], ['10', '12'])).
% 0.45/0.71  thf('30', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 0.45/0.71      inference('clc', [status(thm)], ['28', '29'])).
% 0.45/0.71  thf('31', plain, (((sk_A) != (sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['0', '30'])).
% 0.45/0.71  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.45/0.71  
% 0.45/0.71  % SZS output end Refutation
% 0.45/0.71  
% 0.45/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
