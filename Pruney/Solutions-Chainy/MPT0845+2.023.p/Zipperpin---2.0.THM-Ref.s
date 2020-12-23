%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YhfVQjD2UE

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:37 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  227 ( 275 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('6',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C_2 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('10',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_A )
      | ~ ( r1_xboole_0 @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( r1_xboole_0 @ ( sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( sk_C_2 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_2 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['13','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YhfVQjD2UE
% 0.16/0.37  % Computer   : n025.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 11:31:51 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.54  % Solved by: fo/fo7.sh
% 0.24/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.54  % done 108 iterations in 0.060s
% 0.24/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.54  % SZS output start Refutation
% 0.24/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.24/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.54  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.24/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.24/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.54  thf(d4_tarski, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.24/0.54       ( ![C:$i]:
% 0.24/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.24/0.54           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.24/0.54  thf('0', plain,
% 0.24/0.54      (![X5 : $i, X9 : $i]:
% 0.24/0.54         (((X9) = (k3_tarski @ X5))
% 0.24/0.54          | (r2_hidden @ (sk_D @ X9 @ X5) @ X5)
% 0.24/0.54          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.24/0.54      inference('cnf', [status(esa)], [d4_tarski])).
% 0.24/0.54  thf(t113_zfmisc_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.54  thf('1', plain,
% 0.24/0.54      (![X12 : $i, X13 : $i]:
% 0.24/0.54         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.24/0.54          | ((X13) != (k1_xboole_0)))),
% 0.24/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.24/0.54  thf('2', plain,
% 0.24/0.54      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.24/0.54  thf(t152_zfmisc_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.24/0.54  thf('3', plain,
% 0.24/0.54      (![X14 : $i, X15 : $i]: ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.24/0.54      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.24/0.54  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.24/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.54  thf('5', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.24/0.54          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['0', '4'])).
% 0.24/0.54  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.24/0.54  thf('6', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.54      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.24/0.54  thf('7', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.24/0.54          | ((X0) = (k1_xboole_0)))),
% 0.24/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.54  thf(t7_tarski, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ~( ( r2_hidden @ A @ B ) & 
% 0.24/0.54          ( ![C:$i]:
% 0.24/0.54            ( ~( ( r2_hidden @ C @ B ) & 
% 0.24/0.54                 ( ![D:$i]:
% 0.24/0.54                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.24/0.54  thf('8', plain,
% 0.24/0.54      (![X16 : $i, X17 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X16 @ X17) | (r2_hidden @ (sk_C_2 @ X17) @ X17))),
% 0.24/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.24/0.54  thf('9', plain,
% 0.24/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.54  thf(t1_mcart_1, conjecture,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.54          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.24/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.54    (~( ![A:$i]:
% 0.24/0.54        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.54             ( ![B:$i]:
% 0.24/0.54               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.24/0.54    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.24/0.54  thf('10', plain,
% 0.24/0.54      (![X19 : $i]: (~ (r2_hidden @ X19 @ sk_A) | ~ (r1_xboole_0 @ X19 @ sk_A))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('11', plain,
% 0.24/0.54      ((((sk_A) = (k1_xboole_0)) | ~ (r1_xboole_0 @ (sk_C_2 @ sk_A) @ sk_A))),
% 0.24/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.54  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('13', plain, (~ (r1_xboole_0 @ (sk_C_2 @ sk_A) @ sk_A)),
% 0.24/0.54      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.24/0.54  thf(t3_xboole_0, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.24/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.54  thf('14', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.54  thf('15', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.54  thf('16', plain,
% 0.24/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X16 @ X17)
% 0.24/0.54          | ~ (r2_hidden @ X18 @ X17)
% 0.24/0.54          | ~ (r2_hidden @ X18 @ (sk_C_2 @ X17)))),
% 0.24/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.24/0.54  thf('17', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X1 @ (sk_C_2 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.24/0.54      inference('condensation', [status(thm)], ['16'])).
% 0.24/0.54  thf('18', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((r1_xboole_0 @ (sk_C_2 @ X0) @ X1)
% 0.24/0.54          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_2 @ X0)) @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['15', '17'])).
% 0.24/0.54  thf('19', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((r1_xboole_0 @ (sk_C_2 @ X0) @ X0)
% 0.24/0.54          | (r1_xboole_0 @ (sk_C_2 @ X0) @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['14', '18'])).
% 0.24/0.54  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_2 @ X0) @ X0)),
% 0.24/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.24/0.54  thf('21', plain, ($false), inference('demod', [status(thm)], ['13', '20'])).
% 0.24/0.54  
% 0.24/0.54  % SZS output end Refutation
% 0.24/0.54  
% 0.24/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
