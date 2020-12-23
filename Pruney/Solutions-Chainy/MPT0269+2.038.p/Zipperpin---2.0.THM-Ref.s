%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cnbkEgeUne

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 381 expanded)
%              Number of equality atoms :   42 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X19 @ X18 ) @ X18 )
      | ( X18
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['7','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( ( sk_C_1 @ X19 @ X18 )
       != X19 )
      | ( X18
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cnbkEgeUne
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:39:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 58 iterations in 0.045s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(t66_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.50             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t41_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (((X18) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X19 @ X18) @ X18)
% 0.20/0.50          | ((X18) = (k1_tarski @ X19)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.50  thf(d5_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | (r2_hidden @ X0 @ X3)
% 0.20/0.50          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (k1_tarski @ X1))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2)
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ k1_xboole_0)
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0))
% 0.20/0.50          | ((sk_A) = (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['0', '4'])).
% 0.20/0.50  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ k1_xboole_0)
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.50          | ((sk_A) = (k1_tarski @ X0)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf(t4_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.50          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.50          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.50          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.50  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('condensation', [status(thm)], ['11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_A) = (k1_tarski @ X0))
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['7', '12'])).
% 0.20/0.50  thf(d1_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.50          | ((X10) = (X7))
% 0.20/0.50          | ((X9) != (k1_tarski @ X7)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X7 : $i, X10 : $i]:
% 0.20/0.50         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_A) = (k1_tarski @ X0)) | ((sk_C_1 @ X0 @ sk_A) = (sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (((X18) = (k1_xboole_0))
% 0.20/0.50          | ((sk_C_1 @ X19 @ X18) != (X19))
% 0.20/0.50          | ((X18) = (k1_tarski @ X19)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_B) != (X0))
% 0.20/0.50          | ((sk_A) = (k1_tarski @ X0))
% 0.20/0.50          | ((sk_A) = (k1_tarski @ X0))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.50  thf('20', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['19', '20', '21'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
