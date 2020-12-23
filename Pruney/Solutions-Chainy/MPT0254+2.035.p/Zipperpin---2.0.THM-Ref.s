%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NMgzNMWetT

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 103 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  265 ( 534 expanded)
%              Number of equality atoms :   36 (  72 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
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
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','13','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['19','23'])).

thf('25',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k2_tarski @ X16 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('29',plain,(
    ! [X13: $i,X16: $i] :
      ( r2_hidden @ X13 @ ( k2_tarski @ X16 @ X13 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NMgzNMWetT
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:43:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 38 iterations in 0.016s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(t49_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf(t7_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.46  thf('5', plain, ((r1_tarski @ sk_B_1 @ k1_xboole_0)),
% 0.20/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf(t12_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.46  thf('7', plain, (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.46  thf('9', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.46  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.46  thf('13', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.46  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('15', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '13', '14'])).
% 0.20/0.46  thf('16', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '13', '14'])).
% 0.20/0.46  thf(t69_enumset1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.20/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.46  thf(l51_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X25 : $i, X26 : $i]:
% 0.20/0.46         ((k3_tarski @ (k2_tarski @ X25 @ X26)) = (k2_xboole_0 @ X25 @ X26))),
% 0.20/0.46      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf(d10_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.46  thf('21', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.20/0.46      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.46  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('24', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '23'])).
% 0.20/0.46  thf('25', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.20/0.46      inference('sup+', [status(thm)], ['16', '24'])).
% 0.20/0.46  thf('26', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['15', '25'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.20/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.46  thf(d2_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.46       ( ![D:$i]:
% 0.20/0.46         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.46         (((X14) != (X13))
% 0.20/0.46          | (r2_hidden @ X14 @ X15)
% 0.20/0.46          | ((X15) != (k2_tarski @ X16 @ X13)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X13 : $i, X16 : $i]: (r2_hidden @ X13 @ (k2_tarski @ X16 @ X13))),
% 0.20/0.46      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.46  thf(d1_xboole_0, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['27', '31'])).
% 0.20/0.46  thf('33', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '32'])).
% 0.20/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.46  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.46  thf('35', plain, ($false), inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
