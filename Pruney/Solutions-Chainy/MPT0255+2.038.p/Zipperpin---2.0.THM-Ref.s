%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R6O3zqBAyI

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:00 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  241 ( 338 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
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
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('18',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','16','17'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X18: $i,X21: $i] :
      ( r2_hidden @ X18 @ ( k2_tarski @ X21 @ X18 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','20'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('23',plain,(
    ! [X18: $i,X21: $i] :
      ( r2_hidden @ X18 @ ( k2_tarski @ X21 @ X18 ) ) ),
    inference(simplify,[status(thm)],['19'])).

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

thf('24',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    $false ),
    inference('sup-',[status(thm)],['21','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R6O3zqBAyI
% 0.17/0.38  % Computer   : n025.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 15:17:51 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 90 iterations in 0.032s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(t50_zfmisc_1, conjecture,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.52        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.24/0.52  thf('0', plain,
% 0.24/0.52      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.24/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.24/0.52  thf(t46_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.24/0.52  thf('4', plain,
% 0.24/0.52      (![X15 : $i, X16 : $i]:
% 0.24/0.52         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.24/0.52  thf('5', plain, (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.24/0.52  thf(l32_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      (![X9 : $i, X10 : $i]:
% 0.24/0.52         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.24/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.24/0.52  thf('7', plain,
% 0.24/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_C_1 @ k1_xboole_0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.52  thf('8', plain, ((r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.24/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.52  thf(t12_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.24/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.24/0.52  thf('10', plain, (((k2_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.52  thf('11', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.24/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.52  thf('12', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.24/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.24/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.24/0.52  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.52  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['11', '14'])).
% 0.24/0.52  thf('16', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['10', '15'])).
% 0.24/0.52  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.52  thf('18', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['2', '16', '17'])).
% 0.24/0.52  thf(d2_tarski, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.24/0.52       ( ![D:$i]:
% 0.24/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.24/0.52         (((X19) != (X18))
% 0.24/0.52          | (r2_hidden @ X19 @ X20)
% 0.24/0.52          | ((X20) != (k2_tarski @ X21 @ X18)))),
% 0.24/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      (![X18 : $i, X21 : $i]: (r2_hidden @ X18 @ (k2_tarski @ X21 @ X18))),
% 0.24/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.24/0.52  thf('21', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.24/0.52      inference('sup+', [status(thm)], ['18', '20'])).
% 0.24/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.24/0.52  thf('22', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.24/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.52  thf('23', plain,
% 0.24/0.52      (![X18 : $i, X21 : $i]: (r2_hidden @ X18 @ (k2_tarski @ X21 @ X18))),
% 0.24/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.24/0.52  thf(t3_xboole_0, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.24/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.24/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.24/0.52          | ~ (r2_hidden @ X4 @ X5)
% 0.24/0.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.24/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.52         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.24/0.52          | ~ (r2_hidden @ X0 @ X2))),
% 0.24/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.24/0.52  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.24/0.52      inference('sup-', [status(thm)], ['22', '25'])).
% 0.24/0.52  thf('27', plain, ($false), inference('sup-', [status(thm)], ['21', '26'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
