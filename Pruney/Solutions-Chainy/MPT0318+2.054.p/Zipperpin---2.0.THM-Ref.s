%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lLgwKu3RgN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 111 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 (1134 expanded)
%              Number of equality atoms :   52 ( 226 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X8 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('14',plain,(
    ! [X11: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','20'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lLgwKu3RgN
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 24 iterations in 0.013s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.44  thf(t130_zfmisc_1, conjecture,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.44       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.44         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i,B:$i]:
% 0.21/0.44        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.44          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.44            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.21/0.44        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.44      inference('split', [status(esa)], ['0'])).
% 0.21/0.44  thf(t113_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X7 : $i, X8 : $i]:
% 0.21/0.44         (((X7) = (k1_xboole_0))
% 0.21/0.44          | ((X8) = (k1_xboole_0))
% 0.21/0.44          | ((k2_zfmisc_1 @ X8 @ X7) != (k1_xboole_0)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.44         | ((sk_A) = (k1_xboole_0))
% 0.21/0.44         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.44      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.44  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.44      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('split', [status(esa)], ['0'])).
% 0.21/0.44  thf('8', plain,
% 0.21/0.44      (![X7 : $i, X8 : $i]:
% 0.21/0.44         (((X7) = (k1_xboole_0))
% 0.21/0.44          | ((X8) = (k1_xboole_0))
% 0.21/0.44          | ((k2_zfmisc_1 @ X8 @ X7) != (k1_xboole_0)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.44  thf('9', plain,
% 0.21/0.44      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.44         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.44         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.44  thf('10', plain,
% 0.21/0.44      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.44  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.44  thf(t16_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.21/0.44          ( ( A ) = ( B ) ) ) ))).
% 0.21/0.44  thf('13', plain,
% 0.21/0.44      (![X10 : $i, X11 : $i]:
% 0.21/0.44         (~ (r1_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11))
% 0.21/0.44          | ((X10) != (X11)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.21/0.44  thf('14', plain,
% 0.21/0.44      (![X11 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X11))),
% 0.21/0.44      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.44  thf('15', plain,
% 0.21/0.44      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.44  thf('16', plain,
% 0.21/0.44      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.44         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.44  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.44  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.44      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.44  thf('18', plain,
% 0.21/0.44      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.21/0.44      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.44  thf('19', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.21/0.44       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.21/0.44      inference('split', [status(esa)], ['0'])).
% 0.21/0.44  thf('20', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.21/0.44      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.21/0.44  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.44      inference('simpl_trail', [status(thm)], ['6', '20'])).
% 0.21/0.44  thf('22', plain,
% 0.21/0.44      (![X11 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X11))),
% 0.21/0.44      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.44  thf('23', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.44  thf('24', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.44      inference('simpl_trail', [status(thm)], ['6', '20'])).
% 0.21/0.44  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.44      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.44  thf('26', plain, ($false),
% 0.21/0.44      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
