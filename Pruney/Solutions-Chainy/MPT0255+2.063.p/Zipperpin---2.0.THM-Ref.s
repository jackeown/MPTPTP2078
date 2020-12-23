%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S70Gywjptc

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  230 ( 356 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
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
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ( r2_hidden @ X13 @ X14 )
      | ( X14
       != ( k2_tarski @ X15 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X12: $i,X15: $i] :
      ( r2_hidden @ X12 @ ( k2_tarski @ X15 @ X12 ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','7'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r2_hidden @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S70Gywjptc
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 104 iterations in 0.073s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(t50_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(d2_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (((X13) != (X12))
% 0.20/0.52          | (r2_hidden @ X13 @ X14)
% 0.20/0.52          | ((X14) != (k2_tarski @ X15 @ X12)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X12 : $i, X15 : $i]: (r2_hidden @ X12 @ (k2_tarski @ X15 @ X12))),
% 0.20/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.52  thf(d3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.52          | (r2_hidden @ X2 @ X4)
% 0.20/0.52          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.52         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (r2_hidden @ X0 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.52  thf('8', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.20/0.52      inference('sup+', [status(thm)], ['2', '7'])).
% 0.20/0.52  thf('9', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.20/0.52      inference('sup+', [status(thm)], ['2', '7'])).
% 0.20/0.52  thf(t38_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         ((r1_tarski @ (k2_tarski @ X21 @ X23) @ X24)
% 0.20/0.52          | ~ (r2_hidden @ X23 @ X24)
% 0.20/0.52          | ~ (r2_hidden @ X21 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.52          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain, ((r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ k1_xboole_0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf('14', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf(t12_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf(t49_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k1_tarski @ X25) @ X26) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['18', '21'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
