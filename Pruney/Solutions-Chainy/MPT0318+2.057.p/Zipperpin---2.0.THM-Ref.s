%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eWVU0p4Ab5

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 ( 431 expanded)
%              Number of equality atoms :   54 (  89 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
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

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['10','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eWVU0p4Ab5
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:02:59 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.45  % Solved by: fo/fo7.sh
% 0.23/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.45  % done 21 iterations in 0.008s
% 0.23/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.45  % SZS output start Refutation
% 0.23/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.45  thf(t130_zfmisc_1, conjecture,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.23/0.45       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.45         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.23/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.45    (~( ![A:$i,B:$i]:
% 0.23/0.45        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.23/0.45          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.45            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.23/0.45    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.23/0.45  thf('0', plain,
% 0.23/0.45      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.23/0.45        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('1', plain,
% 0.23/0.45      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.23/0.45      inference('split', [status(esa)], ['0'])).
% 0.23/0.45  thf(t113_zfmisc_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.45  thf('2', plain,
% 0.23/0.45      (![X4 : $i, X5 : $i]:
% 0.23/0.45         (((X4) = (k1_xboole_0))
% 0.23/0.45          | ((X5) = (k1_xboole_0))
% 0.23/0.45          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 0.23/0.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.45  thf('3', plain,
% 0.23/0.45      (((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.45         | ((sk_A) = (k1_xboole_0))
% 0.23/0.45         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.23/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.45  thf('4', plain,
% 0.23/0.45      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.23/0.45      inference('simplify', [status(thm)], ['3'])).
% 0.23/0.45  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('6', plain,
% 0.23/0.45      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.23/0.45      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.23/0.45  thf(t1_boole, axiom,
% 0.23/0.45    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.45  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.45      inference('cnf', [status(esa)], [t1_boole])).
% 0.23/0.45  thf(t49_zfmisc_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.23/0.45  thf('8', plain,
% 0.23/0.45      (![X7 : $i, X8 : $i]:
% 0.23/0.45         ((k2_xboole_0 @ (k1_tarski @ X7) @ X8) != (k1_xboole_0))),
% 0.23/0.45      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.23/0.45  thf('9', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.23/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.45  thf('10', plain,
% 0.23/0.45      (($false)
% 0.23/0.45         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.23/0.45      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.23/0.45  thf('11', plain,
% 0.23/0.45      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.23/0.45      inference('split', [status(esa)], ['0'])).
% 0.23/0.45  thf('12', plain,
% 0.23/0.45      (![X4 : $i, X5 : $i]:
% 0.23/0.45         (((X4) = (k1_xboole_0))
% 0.23/0.45          | ((X5) = (k1_xboole_0))
% 0.23/0.45          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 0.23/0.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.45  thf('13', plain,
% 0.23/0.45      (((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.45         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.23/0.45         | ((sk_A) = (k1_xboole_0))))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.23/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.45  thf('14', plain,
% 0.23/0.45      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.23/0.45      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.45  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('16', plain,
% 0.23/0.45      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.23/0.45      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.23/0.45  thf('17', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.23/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.45  thf('18', plain,
% 0.23/0.45      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.23/0.45         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.23/0.45      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.45  thf('19', plain,
% 0.23/0.45      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.23/0.45      inference('simplify', [status(thm)], ['18'])).
% 0.23/0.45  thf('20', plain,
% 0.23/0.45      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.23/0.45       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.23/0.45      inference('split', [status(esa)], ['0'])).
% 0.23/0.45  thf('21', plain,
% 0.23/0.45      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.23/0.45      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.23/0.45  thf('22', plain, ($false),
% 0.23/0.45      inference('simpl_trail', [status(thm)], ['10', '21'])).
% 0.23/0.45  
% 0.23/0.45  % SZS output end Refutation
% 0.23/0.45  
% 0.23/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
