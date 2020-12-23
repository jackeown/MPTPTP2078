%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cOz1QKejgL

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 194 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  437 (1906 expanded)
%              Number of equality atoms :   84 ( 359 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X8 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X10 @ X12 ) @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_B @ X0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X8 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_B @ X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('29',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i] : ( sk_A != X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ X0 ) ),
    inference(simpl_trail,[status(thm)],['13','34'])).

thf('36',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('37',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cOz1QKejgL
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 79 iterations in 0.048s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(t130_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf(t113_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (((X7) = (k1_xboole_0))
% 0.20/0.50          | ((X8) = (k1_xboole_0))
% 0.20/0.50          | ((k2_zfmisc_1 @ X8 @ X7) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.50  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('7', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t73_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         ((r2_hidden @ X10 @ X11)
% 0.20/0.50          | ((k4_xboole_0 @ (k2_tarski @ X10 @ X12) @ X11) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.20/0.50           | (r2_hidden @ sk_B @ X0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.50  thf(t4_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_B @ X0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((![X0 : $i]: (r2_hidden @ sk_B @ X0))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (((X7) = (k1_xboole_0))
% 0.20/0.50          | ((X8) = (k1_xboole_0))
% 0.20/0.50          | ((k2_zfmisc_1 @ X8 @ X7) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.50  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.20/0.50           | (r2_hidden @ sk_B @ X0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_B @ X0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((![X0 : $i]: (r2_hidden @ sk_B @ X0))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.50  thf(d1_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X1 : $i, X4 : $i]:
% 0.20/0.50         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((![X0 : $i]: ((sk_A) != (X0)))
% 0.20/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.20/0.50       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, (![X0 : $i]: (r2_hidden @ sk_B @ X0)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['13', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X1 : $i, X4 : $i]:
% 0.20/0.50         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.50  thf('37', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('39', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
