%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SWFq3x72Rp

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 209 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) )
        = ( k1_tarski @ X7 ) )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('2',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 != X6 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X6 ) )
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X6 ) )
     != ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X6 ) )
     != ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X3 ) @ X5 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X6 ) ) ),
    inference(demod,[status(thm)],['6','12'])).

thf('14',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SWFq3x72Rp
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 21 iterations in 0.013s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(t21_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46         ( k1_xboole_0 ) ) =>
% 0.20/0.46       ( ( A ) = ( B ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46            ( k1_xboole_0 ) ) =>
% 0.20/0.46          ( ( A ) = ( B ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t20_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46         ( k1_tarski @ A ) ) <=>
% 0.20/0.46       ( ( A ) != ( B ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i]:
% 0.20/0.46         (((k4_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X8))
% 0.20/0.46            = (k1_tarski @ X7))
% 0.20/0.46          | ((X7) = (X8)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.46  thf('2', plain, ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain, (((sk_A) != (sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (((X7) != (X6))
% 0.20/0.46          | ((k4_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X6))
% 0.20/0.46              != (k1_tarski @ X7)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X6 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X6))
% 0.20/0.46           != (k1_tarski @ X6))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf(l33_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.46       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X2 : $i]:
% 0.20/0.46         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X0))
% 0.20/0.46          | (r2_hidden @ X0 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X6 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X6))
% 0.20/0.46           != (k1_tarski @ X6))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.46          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.46  thf(l35_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.46       ( r2_hidden @ A @ B ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X3 : $i, X5 : $i]:
% 0.20/0.46         (((k4_xboole_0 @ (k1_tarski @ X3) @ X5) = (k1_xboole_0))
% 0.20/0.46          | ~ (r2_hidden @ X3 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain, (![X6 : $i]: ((k1_xboole_0) != (k1_tarski @ X6))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '12'])).
% 0.20/0.46  thf('14', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '13'])).
% 0.20/0.46  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
