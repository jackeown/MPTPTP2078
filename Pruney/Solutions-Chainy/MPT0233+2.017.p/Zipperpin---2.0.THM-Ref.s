%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cBvgww1gOG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:39 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  267 ( 341 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X32 )
      | ( r2_hidden @ X30 @ X31 )
      | ( X31
       != ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X29: $i,X32: $i] :
      ( r2_hidden @ X32 @ ( k2_tarski @ X32 @ X29 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X29: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X31 )
      | ( X33 = X32 )
      | ( X33 = X29 )
      | ( X31
       != ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X29: $i,X32: $i,X33: $i] :
      ( ( X33 = X29 )
      | ( X33 = X32 )
      | ~ ( r2_hidden @ X33 @ ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    sk_A != sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cBvgww1gOG
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 608 iterations in 0.227s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.66  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(t70_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf(d2_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.66       ( ![D:$i]:
% 0.46/0.66         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.66         (((X30) != (X32))
% 0.46/0.66          | (r2_hidden @ X30 @ X31)
% 0.46/0.66          | ((X31) != (k2_tarski @ X32 @ X29)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X29 : $i, X32 : $i]: (r2_hidden @ X32 @ (k2_tarski @ X32 @ X29))),
% 0.46/0.66      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['0', '2'])).
% 0.46/0.66  thf(t28_zfmisc_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.66          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.66             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_2))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(l32_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X11 : $i, X13 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.46/0.66          | ~ (r1_tarski @ X11 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.46/0.66         (k2_tarski @ sk_C_1 @ sk_D_2)) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf(t48_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.46/0.66           = (k3_xboole_0 @ X20 @ X21))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.46/0.66         = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.46/0.66            (k2_tarski @ sk_C_1 @ sk_D_2)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(t3_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.66  thf('9', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (((k2_tarski @ sk_A @ sk_B_1)
% 0.46/0.66         = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.46/0.66            (k2_tarski @ sk_C_1 @ sk_D_2)))),
% 0.46/0.66      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf(d4_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.46/0.66       ( ![D:$i]:
% 0.46/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.66           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X9 @ X8)
% 0.46/0.66          | (r2_hidden @ X9 @ X7)
% 0.46/0.66          | ((X8) != (k3_xboole_0 @ X6 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.46/0.66         ((r2_hidden @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.46/0.66          | (r2_hidden @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1))
% 0.46/0.66          | (r2_hidden @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_2)))),
% 0.46/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('16', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X29 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X33 @ X31)
% 0.46/0.66          | ((X33) = (X32))
% 0.46/0.66          | ((X33) = (X29))
% 0.46/0.66          | ((X31) != (k2_tarski @ X32 @ X29)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X29 : $i, X32 : $i, X33 : $i]:
% 0.46/0.66         (((X33) = (X29))
% 0.46/0.66          | ((X33) = (X32))
% 0.46/0.66          | ~ (r2_hidden @ X33 @ (k2_tarski @ X32 @ X29)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.66  thf('19', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '18'])).
% 0.46/0.66  thf('20', plain, (((sk_A) != (sk_D_2))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('21', plain, (((sk_A) != (sk_C_1))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('22', plain, ($false),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['19', '20', '21'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.50/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
