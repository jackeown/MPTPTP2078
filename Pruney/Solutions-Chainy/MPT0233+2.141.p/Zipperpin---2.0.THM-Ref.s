%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JuMKlmQvRN

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  176 ( 242 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X11 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('1',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_2 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D_2 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    sk_A != sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JuMKlmQvRN
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 106 iterations in 0.087s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(d2_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((X9) != (X11))
% 0.21/0.54          | (r2_hidden @ X9 @ X10)
% 0.21/0.54          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X8 : $i, X11 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X11 @ X8))),
% 0.21/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.54  thf(t28_zfmisc_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.21/0.54          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.21/0.54             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_2))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t28_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_2))
% 0.21/0.54         = (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf(d4_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.54          | (r2_hidden @ X4 @ X2)
% 0.21/0.54          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.54         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.54          | (r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D_2)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.54  thf('8', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X12 @ X10)
% 0.21/0.54          | ((X12) = (X11))
% 0.21/0.54          | ((X12) = (X8))
% 0.21/0.54          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X8 : $i, X11 : $i, X12 : $i]:
% 0.21/0.54         (((X12) = (X8))
% 0.21/0.54          | ((X12) = (X11))
% 0.21/0.54          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.54  thf('11', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_D_2)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.54  thf('12', plain, (((sk_A) != (sk_D_2))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain, (((sk_A) != (sk_C))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['11', '12', '13'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
