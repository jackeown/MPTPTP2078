%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dQbuv4lmhy

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  165 ( 190 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X18: $i,X21: $i] :
      ( r2_hidden @ X18 @ ( k2_tarski @ X21 @ X18 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k2_xboole_0 @ X9 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('10',plain,(
    ! [X18: $i,X21: $i] :
      ( r2_hidden @ X18 @ ( k2_tarski @ X21 @ X18 ) ) ),
    inference(simplify,[status(thm)],['3'])).

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

thf('11',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    $false ),
    inference('sup-',[status(thm)],['8','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dQbuv4lmhy
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 48 iterations in 0.047s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(t50_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_C_2 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(d2_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         (((X19) != (X18))
% 0.20/0.52          | (r2_hidden @ X19 @ X20)
% 0.20/0.52          | ((X20) != (k2_tarski @ X21 @ X18)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X18 : $i, X21 : $i]: (r2_hidden @ X18 @ (k2_tarski @ X21 @ X18))),
% 0.20/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.52  thf(d3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.52          | (r2_hidden @ X6 @ X8)
% 0.20/0.52          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.52         ((r2_hidden @ X6 @ (k2_xboole_0 @ X9 @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.20/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (r2_hidden @ X0 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.52  thf('8', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.20/0.52      inference('sup+', [status(thm)], ['2', '7'])).
% 0.20/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.52  thf('9', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X18 : $i, X21 : $i]: (r2_hidden @ X18 @ (k2_tarski @ X21 @ X18))),
% 0.20/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.52  thf(t3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X14 @ X12)
% 0.20/0.52          | ~ (r2_hidden @ X14 @ X15)
% 0.20/0.52          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ X2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.52  thf('14', plain, ($false), inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
