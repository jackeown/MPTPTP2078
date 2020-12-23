%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dlaIkQ1Cpq

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:01 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 ( 413 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ ( k2_tarski @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','9'])).

thf('12',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X22 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r2_hidden @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dlaIkQ1Cpq
% 0.12/0.35  % Computer   : n001.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 13:03:30 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.77/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.98  % Solved by: fo/fo7.sh
% 0.77/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.98  % done 385 iterations in 0.515s
% 0.77/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.98  % SZS output start Refutation
% 0.77/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.98  thf(t50_zfmisc_1, conjecture,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.77/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.98        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.77/0.98    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.77/0.98  thf('0', plain,
% 0.77/0.98      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(commutativity_k2_xboole_0, axiom,
% 0.77/0.98    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.77/0.98  thf('1', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.98  thf('2', plain,
% 0.77/0.98      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.77/0.98      inference('demod', [status(thm)], ['0', '1'])).
% 0.77/0.98  thf(d10_xboole_0, axiom,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.98  thf('3', plain,
% 0.77/0.98      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.77/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.98  thf('4', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.77/0.98      inference('simplify', [status(thm)], ['3'])).
% 0.77/0.98  thf(t38_zfmisc_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.77/0.98       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.77/0.98  thf('5', plain,
% 0.77/0.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.98         ((r2_hidden @ X22 @ X23)
% 0.77/0.98          | ~ (r1_tarski @ (k2_tarski @ X22 @ X24) @ X23))),
% 0.77/0.98      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.77/0.98  thf('6', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.98  thf(d3_xboole_0, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.77/0.98       ( ![D:$i]:
% 0.77/0.98         ( ( r2_hidden @ D @ C ) <=>
% 0.77/0.98           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.77/0.98  thf('7', plain,
% 0.77/0.98      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X2 @ X3)
% 0.77/0.98          | (r2_hidden @ X2 @ X4)
% 0.77/0.98          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.77/0.98      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.77/0.98  thf('8', plain,
% 0.77/0.98      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.77/0.98         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.77/0.98      inference('simplify', [status(thm)], ['7'])).
% 0.77/0.98  thf('9', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         (r2_hidden @ X1 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['6', '8'])).
% 0.77/0.98  thf('10', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.77/0.98      inference('sup+', [status(thm)], ['2', '9'])).
% 0.77/0.98  thf('11', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.77/0.98      inference('sup+', [status(thm)], ['2', '9'])).
% 0.77/0.98  thf('12', plain,
% 0.77/0.98      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.77/0.98         ((r1_tarski @ (k2_tarski @ X22 @ X24) @ X25)
% 0.77/0.98          | ~ (r2_hidden @ X24 @ X25)
% 0.77/0.98          | ~ (r2_hidden @ X22 @ X25))),
% 0.77/0.98      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.77/0.98  thf('13', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.77/0.98          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ k1_xboole_0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['11', '12'])).
% 0.77/0.98  thf('14', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0)),
% 0.77/0.98      inference('sup-', [status(thm)], ['10', '13'])).
% 0.77/0.98  thf(t69_enumset1, axiom,
% 0.77/0.98    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.77/0.98  thf('15', plain,
% 0.77/0.98      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.77/0.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.98  thf('16', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.77/0.98      inference('demod', [status(thm)], ['14', '15'])).
% 0.77/0.98  thf('17', plain,
% 0.77/0.98      (![X8 : $i, X10 : $i]:
% 0.77/0.98         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.77/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.98  thf('18', plain,
% 0.77/0.98      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.77/0.98        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/0.98  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.77/0.98  thf('19', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.77/0.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.77/0.98  thf('20', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.77/0.98      inference('demod', [status(thm)], ['18', '19'])).
% 0.77/0.98  thf('21', plain,
% 0.77/0.98      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.77/0.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.98  thf(t41_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( k2_tarski @ A @ B ) =
% 0.77/0.98       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.77/0.98  thf('22', plain,
% 0.77/0.98      (![X12 : $i, X13 : $i]:
% 0.77/0.98         ((k2_tarski @ X12 @ X13)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.77/0.98      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.77/0.98  thf('23', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.98  thf(t49_zfmisc_1, axiom,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.77/0.98  thf('24', plain,
% 0.77/0.98      (![X26 : $i, X27 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X26) @ X27) != (k1_xboole_0))),
% 0.77/0.98      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.77/0.98  thf('25', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.98  thf('26', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['22', '25'])).
% 0.77/0.98  thf('27', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['21', '26'])).
% 0.77/0.98  thf('28', plain, ($false),
% 0.77/0.98      inference('simplify_reflect-', [status(thm)], ['20', '27'])).
% 0.77/0.98  
% 0.77/0.98  % SZS output end Refutation
% 0.77/0.98  
% 0.77/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
