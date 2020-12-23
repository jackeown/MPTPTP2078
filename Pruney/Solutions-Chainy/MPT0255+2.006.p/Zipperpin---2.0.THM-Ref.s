%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HPrq6UgfF8

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  64 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  268 ( 314 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['3','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k2_tarski @ X27 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k2_tarski @ X27 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    $false ),
    inference('sup-',[status(thm)],['24','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HPrq6UgfF8
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:13:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 53 iterations in 0.040s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(t50_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fc5_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X9 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.20/0.50  thf('3', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.50  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('5', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf(l13_xboole_0, axiom,
% 0.20/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.50  thf('7', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.50  thf(commutativity_k2_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.50  thf(l51_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         ((k3_tarski @ (k2_tarski @ X25 @ X26)) = (k2_xboole_0 @ X25 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         ((k3_tarski @ (k2_tarski @ X25 @ X26)) = (k2_xboole_0 @ X25 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X9 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.50        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('18', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.50  thf('20', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf(t38_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.50         ((r2_hidden @ X27 @ X28)
% 0.20/0.50          | ~ (r1_tarski @ (k2_tarski @ X27 @ X29) @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('23', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('24', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.50  thf('25', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('27', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.20/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.50         ((r2_hidden @ X27 @ X28)
% 0.20/0.50          | ~ (r1_tarski @ (k2_tarski @ X27 @ X29) @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf(t3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ X1)
% 0.20/0.50          | ~ (r2_hidden @ X3 @ X4)
% 0.20/0.50          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.50          | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.50  thf('33', plain, ($false), inference('sup-', [status(thm)], ['24', '32'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
