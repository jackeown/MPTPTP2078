%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qmSnC7GUQJ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  78 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  279 ( 695 expanded)
%              Number of equality atoms :   39 (  85 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t67_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_mcart_1])).

thf('0',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( X6
        = ( k4_tarski @ ( sk_E @ X6 @ X5 @ X4 ) @ ( sk_F @ X6 @ X5 @ X4 ) ) )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7
       != ( k2_mcart_1 @ X7 ) )
      | ( X7
       != ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_tarski @ X8 @ X9 )
     != ( k2_mcart_1 @ ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) )
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('12',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['1','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7
       != ( k1_mcart_1 @ X7 ) )
      | ( X7
       != ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_tarski @ X8 @ X9 )
     != ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) )
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('20',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['13','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qmSnC7GUQJ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 17 iterations in 0.012s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.46  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(t67_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.46       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.46        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.46          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t67_mcart_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d10_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.46  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.46      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.46  thf(t103_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.46          ( r2_hidden @ D @ A ) & 
% 0.20/0.46          ( ![E:$i,F:$i]:
% 0.20/0.46            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.46                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.46         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X4 @ X5))
% 0.20/0.46          | ((X6) = (k4_tarski @ (sk_E @ X6 @ X5 @ X4) @ (sk_F @ X6 @ X5 @ X4)))
% 0.20/0.46          | ~ (r2_hidden @ X6 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.46          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (((sk_A)
% 0.20/0.46         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.20/0.46            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.46  thf(t20_mcart_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.47       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (((X7) != (k2_mcart_1 @ X7)) | ((X7) != (k4_tarski @ X8 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         ((k4_tarski @ X8 @ X9) != (k2_mcart_1 @ (k4_tarski @ X8 @ X9)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ (sk_F @ sk_A @ sk_C @ sk_B))
% 0.20/0.47         != (k2_mcart_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (((sk_A)
% 0.20/0.47         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.20/0.47            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.47  thf('12', plain, (((sk_A) != (k2_mcart_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['1', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((sk_A)
% 0.20/0.47         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.20/0.47            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (((X7) != (k1_mcart_1 @ X7)) | ((X7) != (k4_tarski @ X8 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         ((k4_tarski @ X8 @ X9) != (k1_mcart_1 @ (k4_tarski @ X8 @ X9)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ (sk_F @ sk_A @ sk_C @ sk_B))
% 0.20/0.47         != (k1_mcart_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (((sk_A)
% 0.20/0.47         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.20/0.47            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.47  thf('20', plain, (((sk_A) != (k1_mcart_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((((sk_A) != (sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '20'])).
% 0.20/0.47  thf('22', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('24', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain, ($false),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['13', '24'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
