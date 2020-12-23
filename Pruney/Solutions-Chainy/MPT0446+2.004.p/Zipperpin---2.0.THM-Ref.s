%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.frUnb9YatO

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  308 ( 528 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t30_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
         => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ( X18
       != ( k2_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ ( k2_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['18','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.frUnb9YatO
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:22:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 114 iterations in 0.062s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.22/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(t30_relat_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ C ) =>
% 0.22/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.22/0.51         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.22/0.51           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ( v1_relat_1 @ C ) =>
% 0.22/0.51          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.22/0.51            ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.22/0.51              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t30_relat_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))
% 0.22/0.51        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('2', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d4_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]:
% 0.22/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 0.22/0.51          | (r2_hidden @ X8 @ X11)
% 0.22/0.51          | ((X11) != (k1_relat_1 @ X10)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.51         ((r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.22/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.51  thf('5', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.51  thf(d6_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( k3_relat_1 @ A ) =
% 0.22/0.51         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X22 : $i]:
% 0.22/0.51         (((k3_relat_1 @ X22)
% 0.22/0.51            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 0.22/0.51          | ~ (v1_relat_1 @ X22))),
% 0.22/0.51      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.51  thf(t7_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf(d3_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X2 @ X3)
% 0.22/0.51          | (r2_hidden @ X2 @ X4)
% 0.22/0.51          | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)) | ~ (v1_relat_1 @ sk_C_3))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '10'])).
% 0.22/0.52  thf('12', plain, ((v1_relat_1 @ sk_C_3)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)))
% 0.22/0.52         <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('15', plain, (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))) | 
% 0.22/0.52       ~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('17', plain, (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain, (~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.22/0.52  thf('19', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d5_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 0.22/0.52          | (r2_hidden @ X16 @ X18)
% 0.22/0.52          | ((X18) != (k2_relat_1 @ X17)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         ((r2_hidden @ X16 @ (k2_relat_1 @ X17))
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.22/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.52  thf('22', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_3))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X22 : $i]:
% 0.22/0.52         (((k3_relat_1 @ X22)
% 0.22/0.52            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 0.22/0.52          | ~ (v1_relat_1 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['23', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X2 @ X3)
% 0.22/0.52          | (r2_hidden @ X2 @ X4)
% 0.22/0.52          | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)) | ~ (v1_relat_1 @ sk_C_3))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '29'])).
% 0.22/0.52  thf('31', plain, ((v1_relat_1 @ sk_C_3)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain, ($false), inference('demod', [status(thm)], ['18', '32'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
