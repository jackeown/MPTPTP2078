%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BP8X9jrQ6C

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 124 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  307 ( 574 expanded)
%              Number of equality atoms :   44 (  71 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(fc4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_xboole_0])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('4',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('8',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('9',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_xboole_0])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_tarski @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('22',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('25',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','33','34'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('36',plain,(
    ! [X65: $i,X66: $i] :
      ( ( X66 != X65 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X66 ) @ ( k1_tarski @ X65 ) )
       != ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('37',plain,(
    ! [X65: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X65 ) @ ( k1_tarski @ X65 ) )
     != ( k1_tarski @ X65 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('38',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X65: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X65 ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BP8X9jrQ6C
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:40:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 258 iterations in 0.113s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.58  thf(t50_zfmisc_1, conjecture,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.58        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(fc4_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.58       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.58  thf('1', plain,
% 0.22/0.58      (![X3 : $i, X4 : $i]:
% 0.22/0.58         ((v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc4_xboole_0])).
% 0.22/0.58  thf('2', plain,
% 0.22/0.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.58        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.58  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.58  thf('4', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.58  thf(l13_xboole_0, axiom,
% 0.22/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.58  thf('5', plain,
% 0.22/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.58  thf('6', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.58  thf('7', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.58  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.58  thf('9', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.22/0.58  thf('10', plain,
% 0.22/0.58      (![X0 : $i]: (((k3_tarski @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.58  thf('11', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.58  thf(l51_zfmisc_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.58  thf('12', plain,
% 0.22/0.58      (![X63 : $i, X64 : $i]:
% 0.22/0.58         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.22/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.58  thf('13', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.58  thf('14', plain,
% 0.22/0.58      (![X3 : $i, X4 : $i]:
% 0.22/0.58         ((v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc4_xboole_0])).
% 0.22/0.58  thf('15', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.58  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.58  thf('17', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.58  thf('18', plain,
% 0.22/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.58  thf('19', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.58  thf('20', plain, (((k2_tarski @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['6', '19'])).
% 0.22/0.58  thf('21', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.58  thf('22', plain,
% 0.22/0.58      (![X63 : $i, X64 : $i]:
% 0.22/0.58         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.22/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.58  thf('23', plain, (((k3_tarski @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.58  thf('24', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.22/0.58  thf('25', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.58  thf('26', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.58  thf('27', plain, (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.22/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.58  thf(fc5_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.58       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      (![X5 : $i, X6 : $i]:
% 0.22/0.58         ((v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.22/0.58  thf('29', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.58  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.58  thf('31', plain, ((v1_xboole_0 @ sk_B)),
% 0.22/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.58  thf('32', plain,
% 0.22/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.58  thf('33', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.58  thf(t69_enumset1, axiom,
% 0.22/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.22/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.58  thf('35', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['20', '33', '34'])).
% 0.22/0.58  thf(t20_zfmisc_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.58         ( k1_tarski @ A ) ) <=>
% 0.22/0.58       ( ( A ) != ( B ) ) ))).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      (![X65 : $i, X66 : $i]:
% 0.22/0.58         (((X66) != (X65))
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X66) @ (k1_tarski @ X65))
% 0.22/0.58              != (k1_tarski @ X66)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      (![X65 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ (k1_tarski @ X65) @ (k1_tarski @ X65))
% 0.22/0.58           != (k1_tarski @ X65))),
% 0.22/0.58      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.58  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.58  thf('38', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.58  thf(t100_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      (![X7 : $i, X8 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X7 @ X8)
% 0.22/0.58           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.58  thf('40', plain,
% 0.22/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.58  thf(t92_xboole_1, axiom,
% 0.22/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.58  thf('41', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['40', '41'])).
% 0.22/0.58  thf('43', plain, (![X65 : $i]: ((k1_xboole_0) != (k1_tarski @ X65))),
% 0.22/0.58      inference('demod', [status(thm)], ['37', '42'])).
% 0.22/0.58  thf('44', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['35', '43'])).
% 0.22/0.58  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
