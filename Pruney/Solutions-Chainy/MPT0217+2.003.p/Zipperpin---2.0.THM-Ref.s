%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W69vPcdk9r

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  24 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  106 ( 172 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t10_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( ( k2_tarski @ A @ B )
          = ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( ( k2_tarski @ A @ B )
            = ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t10_zfmisc_1])).

thf('0',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X8 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','7','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W69vPcdk9r
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 20 iterations in 0.014s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.44  thf(t10_zfmisc_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.44     ( ~( ( ( k2_tarski @ A @ B ) = ( k2_tarski @ C @ D ) ) & 
% 0.20/0.44          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.44        ( ~( ( ( k2_tarski @ A @ B ) = ( k2_tarski @ C @ D ) ) & 
% 0.20/0.44             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t10_zfmisc_1])).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(d2_tarski, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.44       ( ![D:$i]:
% 0.20/0.44         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.44         (((X6) != (X8))
% 0.20/0.44          | (r2_hidden @ X6 @ X7)
% 0.20/0.44          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X5 : $i, X8 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X8 @ X5))),
% 0.20/0.44      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.44  thf('3', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.20/0.44      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X9 @ X7)
% 0.20/0.44          | ((X9) = (X8))
% 0.20/0.44          | ((X9) = (X5))
% 0.20/0.44          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.20/0.44         (((X9) = (X5))
% 0.20/0.44          | ((X9) = (X8))
% 0.20/0.44          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 0.20/0.44      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.44  thf('6', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.44  thf('7', plain, (((sk_A) != (sk_D_1))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('8', plain, (((sk_A) != (sk_C_1))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('9', plain, ($false),
% 0.20/0.44      inference('simplify_reflect-', [status(thm)], ['6', '7', '8'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
