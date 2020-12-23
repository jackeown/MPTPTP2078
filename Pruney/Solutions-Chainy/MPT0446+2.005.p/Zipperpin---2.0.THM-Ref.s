%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gtt8hpXt9d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  292 ( 587 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

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
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( ( k3_relat_1 @ X8 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( ( k3_relat_1 @ X8 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['21','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gtt8hpXt9d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:34:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 57 iterations in 0.028s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.48  thf(t30_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.48         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.48           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ C ) =>
% 0.21/0.48          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.48            ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.48              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t30_relat_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.21/0.48        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(d6_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k3_relat_1 @ A ) =
% 0.21/0.48         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         (((k3_relat_1 @ X8)
% 0.21/0.48            = (k2_xboole_0 @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X8)))
% 0.21/0.48          | ~ (v1_relat_1 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.21/0.48  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t20_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.48         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.48           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.21/0.48          | (r2_hidden @ X10 @ (k2_relat_1 @ X11))
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.48  thf(t7_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | (r2_hidden @ X2 @ X4)
% 0.21/0.48          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (r2_hidden @ sk_B @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '13'])).
% 0.21/0.48  thf('15', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('18', plain, (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))) | 
% 0.21/0.48       ~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('20', plain, (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, (~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.21/0.48  thf('22', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.21/0.48          | (r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         (((k3_relat_1 @ X8)
% 0.21/0.48            = (k2_xboole_0 @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X8)))
% 0.21/0.48          | ~ (v1_relat_1 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | (r2_hidden @ X2 @ X4)
% 0.21/0.48          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '31'])).
% 0.21/0.48  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain, ($false), inference('demod', [status(thm)], ['21', '34'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
