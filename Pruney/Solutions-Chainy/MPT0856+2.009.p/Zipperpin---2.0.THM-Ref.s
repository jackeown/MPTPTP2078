%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fTDyJ5Wobd

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:43 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 425 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( r2_hidden @ X19 @ ( k1_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k4_xboole_0 @ X15 @ ( k1_tarski @ X17 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ X12 )
        = X12 )
      | ~ ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_ordinal1 @ X1 ) @ ( k1_tarski @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_ordinal1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t12_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_mcart_1])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('7',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_B ) @ ( k1_tarski @ X0 ) ) )
      | ( sk_B = X0 ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X16 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X15 @ ( k1_tarski @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X15 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('19',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(split,[status(esa)],['15'])).

thf('23',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['16','23'])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fTDyJ5Wobd
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.81/2.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.81/2.04  % Solved by: fo/fo7.sh
% 1.81/2.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.81/2.04  % done 2197 iterations in 1.593s
% 1.81/2.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.81/2.04  % SZS output start Refutation
% 1.81/2.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.81/2.04  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.81/2.04  thf(sk_A_type, type, sk_A: $i).
% 1.81/2.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.81/2.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.81/2.04  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.81/2.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.81/2.04  thf(sk_B_type, type, sk_B: $i).
% 1.81/2.04  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.81/2.04  thf(sk_C_type, type, sk_C: $i).
% 1.81/2.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.81/2.04  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 1.81/2.04  thf('0', plain, (![X19 : $i]: (r2_hidden @ X19 @ (k1_ordinal1 @ X19))),
% 1.81/2.04      inference('cnf', [status(esa)], [t10_ordinal1])).
% 1.81/2.04  thf(t64_zfmisc_1, axiom,
% 1.81/2.04    (![A:$i,B:$i,C:$i]:
% 1.81/2.04     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.81/2.04       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.81/2.04  thf('1', plain,
% 1.81/2.04      (![X14 : $i, X15 : $i, X17 : $i]:
% 1.81/2.04         ((r2_hidden @ X14 @ (k4_xboole_0 @ X15 @ (k1_tarski @ X17)))
% 1.81/2.04          | ((X14) = (X17))
% 1.81/2.04          | ~ (r2_hidden @ X14 @ X15))),
% 1.81/2.04      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.81/2.04  thf('2', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i]:
% 1.81/2.04         (((X0) = (X1))
% 1.81/2.04          | (r2_hidden @ X0 @ 
% 1.81/2.04             (k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X1))))),
% 1.81/2.04      inference('sup-', [status(thm)], ['0', '1'])).
% 1.81/2.04  thf(l22_zfmisc_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( r2_hidden @ A @ B ) =>
% 1.81/2.04       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 1.81/2.04  thf('3', plain,
% 1.81/2.04      (![X12 : $i, X13 : $i]:
% 1.81/2.04         (((k2_xboole_0 @ (k1_tarski @ X13) @ X12) = (X12))
% 1.81/2.04          | ~ (r2_hidden @ X13 @ X12))),
% 1.81/2.04      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 1.81/2.04  thf('4', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i]:
% 1.81/2.04         (((X1) = (X0))
% 1.81/2.04          | ((k2_xboole_0 @ (k1_tarski @ X1) @ 
% 1.81/2.04              (k4_xboole_0 @ (k1_ordinal1 @ X1) @ (k1_tarski @ X0)))
% 1.81/2.04              = (k4_xboole_0 @ (k1_ordinal1 @ X1) @ (k1_tarski @ X0))))),
% 1.81/2.04      inference('sup-', [status(thm)], ['2', '3'])).
% 1.81/2.04  thf(t12_mcart_1, conjecture,
% 1.81/2.04    (![A:$i,B:$i,C:$i]:
% 1.81/2.04     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 1.81/2.04       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 1.81/2.04         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.81/2.04  thf(zf_stmt_0, negated_conjecture,
% 1.81/2.04    (~( ![A:$i,B:$i,C:$i]:
% 1.81/2.04        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 1.81/2.04          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 1.81/2.04            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 1.81/2.04    inference('cnf.neg', [status(esa)], [t12_mcart_1])).
% 1.81/2.04  thf('5', plain,
% 1.81/2.04      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))),
% 1.81/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.04  thf(t10_mcart_1, axiom,
% 1.81/2.04    (![A:$i,B:$i,C:$i]:
% 1.81/2.04     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.81/2.04       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.81/2.04         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.81/2.04  thf('6', plain,
% 1.81/2.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.81/2.04         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 1.81/2.04          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 1.81/2.04      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.81/2.04  thf('7', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 1.81/2.04      inference('sup-', [status(thm)], ['5', '6'])).
% 1.81/2.04  thf(d3_xboole_0, axiom,
% 1.81/2.04    (![A:$i,B:$i,C:$i]:
% 1.81/2.04     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.81/2.04       ( ![D:$i]:
% 1.81/2.04         ( ( r2_hidden @ D @ C ) <=>
% 1.81/2.04           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.81/2.04  thf('8', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.81/2.04         (~ (r2_hidden @ X0 @ X3)
% 1.81/2.04          | (r2_hidden @ X0 @ X2)
% 1.81/2.04          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.81/2.04      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.81/2.04  thf('9', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.81/2.04         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.81/2.04      inference('simplify', [status(thm)], ['8'])).
% 1.81/2.04  thf('10', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 1.81/2.04          (k2_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 1.81/2.04      inference('sup-', [status(thm)], ['7', '9'])).
% 1.81/2.04  thf('11', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 1.81/2.04           (k4_xboole_0 @ (k1_ordinal1 @ sk_B) @ (k1_tarski @ X0)))
% 1.81/2.04          | ((sk_B) = (X0)))),
% 1.81/2.04      inference('sup+', [status(thm)], ['4', '10'])).
% 1.81/2.04  thf('12', plain,
% 1.81/2.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.81/2.04         (((X14) != (X16))
% 1.81/2.04          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X15 @ (k1_tarski @ X16))))),
% 1.81/2.04      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.81/2.04  thf('13', plain,
% 1.81/2.04      (![X15 : $i, X16 : $i]:
% 1.81/2.04         ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X15 @ (k1_tarski @ X16)))),
% 1.81/2.04      inference('simplify', [status(thm)], ['12'])).
% 1.81/2.04  thf('14', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 1.81/2.04      inference('sup-', [status(thm)], ['11', '13'])).
% 1.81/2.04  thf('15', plain,
% 1.81/2.04      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 1.81/2.04        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))),
% 1.81/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.04  thf('16', plain,
% 1.81/2.04      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 1.81/2.04         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 1.81/2.04      inference('split', [status(esa)], ['15'])).
% 1.81/2.04  thf('17', plain,
% 1.81/2.04      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))),
% 1.81/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.04  thf('18', plain,
% 1.81/2.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.81/2.04         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 1.81/2.04          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 1.81/2.04      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.81/2.04  thf('19', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)),
% 1.81/2.04      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.04  thf('20', plain,
% 1.81/2.04      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))
% 1.81/2.04         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)))),
% 1.81/2.04      inference('split', [status(esa)], ['15'])).
% 1.81/2.04  thf('21', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))),
% 1.81/2.04      inference('sup-', [status(thm)], ['19', '20'])).
% 1.81/2.04  thf('22', plain,
% 1.81/2.04      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 1.81/2.04       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))),
% 1.81/2.04      inference('split', [status(esa)], ['15'])).
% 1.81/2.04  thf('23', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 1.81/2.04      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 1.81/2.04  thf('24', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 1.81/2.04      inference('simpl_trail', [status(thm)], ['16', '23'])).
% 1.81/2.04  thf('25', plain, ($false),
% 1.81/2.04      inference('simplify_reflect-', [status(thm)], ['14', '24'])).
% 1.81/2.04  
% 1.81/2.04  % SZS output end Refutation
% 1.81/2.04  
% 1.81/2.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
