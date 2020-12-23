%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TePbAm23BT

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  58 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  242 ( 277 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
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

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('25',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('26',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    $false ),
    inference('sup-',[status(thm)],['18','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TePbAm23BT
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 48 iterations in 0.024s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.44  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.44  thf(t50_zfmisc_1, conjecture,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.44        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(fc5_xboole_0, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.44       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X5 : $i, X6 : $i]:
% 0.21/0.44         ((v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.21/0.44      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.21/0.44  thf('3', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C_1))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.44  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.44  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.44  thf('5', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.21/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.44  thf(l13_xboole_0, axiom,
% 0.21/0.44    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.44  thf('7', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.44  thf('8', plain,
% 0.21/0.44      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.44      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.44  thf(commutativity_k2_tarski, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.44  thf('9', plain,
% 0.21/0.44      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.21/0.44      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.44  thf(l51_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.44  thf('10', plain,
% 0.21/0.44      (![X26 : $i, X27 : $i]:
% 0.21/0.44         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.21/0.44      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.44      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      (![X26 : $i, X27 : $i]:
% 0.21/0.44         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.21/0.44      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.44  thf('13', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.44      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.44  thf('14', plain,
% 0.21/0.44      (((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.44      inference('demod', [status(thm)], ['8', '13'])).
% 0.21/0.44  thf('15', plain,
% 0.21/0.44      (![X5 : $i, X6 : $i]:
% 0.21/0.44         ((v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.21/0.44      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.21/0.44  thf('16', plain,
% 0.21/0.44      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.44        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.44  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.44  thf('18', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.44      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.44  thf(d2_tarski, axiom,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.44       ( ![D:$i]:
% 0.21/0.44         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.44  thf('19', plain,
% 0.21/0.44      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.44         (((X12) != (X11))
% 0.21/0.44          | (r2_hidden @ X12 @ X13)
% 0.21/0.44          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.21/0.44      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.44  thf('20', plain,
% 0.21/0.44      (![X11 : $i, X14 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X14 @ X11))),
% 0.21/0.44      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.44  thf('21', plain,
% 0.21/0.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.44  thf(t2_boole, axiom,
% 0.21/0.44    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.44  thf('22', plain,
% 0.21/0.44      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.44  thf(t4_xboole_0, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.44            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.44  thf('23', plain,
% 0.21/0.44      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.21/0.44          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.21/0.44      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.44  thf('24', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.44  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.44  thf('25', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.44      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.44  thf('26', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.44      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.44  thf('27', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['21', '26'])).
% 0.21/0.44  thf('28', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['20', '27'])).
% 0.21/0.44  thf('29', plain, ($false), inference('sup-', [status(thm)], ['18', '28'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
