%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V0QbEZATzX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:17 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   45 (  88 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  315 ( 795 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t219_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
          <=> ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
            <=> ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t219_relat_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
   <= ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ~ ( r1_tarski @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('16',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','12','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['15','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t210_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( ( r1_tarski @ C @ B )
           => ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k7_relat_1 @ X10 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t210_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['14','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V0QbEZATzX
% 0.16/0.37  % Computer   : n025.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:47:21 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.25/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.47  % Solved by: fo/fo7.sh
% 0.25/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.47  % done 43 iterations in 0.015s
% 0.25/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.47  % SZS output start Refutation
% 0.25/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.25/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.25/0.47  thf(t219_relat_1, conjecture,
% 0.25/0.47    (![A:$i]:
% 0.25/0.47     ( ( v1_relat_1 @ A ) =>
% 0.25/0.47       ( ![B:$i]:
% 0.25/0.47         ( ( v1_relat_1 @ B ) =>
% 0.25/0.47           ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.47             ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ))).
% 0.25/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.47    (~( ![A:$i]:
% 0.25/0.47        ( ( v1_relat_1 @ A ) =>
% 0.25/0.47          ( ![B:$i]:
% 0.25/0.47            ( ( v1_relat_1 @ B ) =>
% 0.25/0.47              ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.47                ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )),
% 0.25/0.47    inference('cnf.neg', [status(esa)], [t219_relat_1])).
% 0.25/0.47  thf('0', plain,
% 0.25/0.47      ((~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.25/0.47        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.25/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.47  thf('1', plain,
% 0.25/0.47      ((~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.25/0.47         <= (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.25/0.47      inference('split', [status(esa)], ['0'])).
% 0.25/0.47  thf('2', plain,
% 0.25/0.47      (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))) | 
% 0.25/0.47       ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.25/0.47      inference('split', [status(esa)], ['0'])).
% 0.25/0.47  thf(t88_relat_1, axiom,
% 0.25/0.47    (![A:$i,B:$i]:
% 0.25/0.47     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.25/0.47  thf('3', plain,
% 0.25/0.47      (![X11 : $i, X12 : $i]:
% 0.25/0.47         ((r1_tarski @ (k7_relat_1 @ X11 @ X12) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.25/0.47      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.25/0.47  thf('4', plain,
% 0.25/0.47      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.25/0.47        | (r1_tarski @ sk_A @ sk_B))),
% 0.25/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.47  thf('5', plain,
% 0.25/0.47      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.25/0.47         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.25/0.47      inference('split', [status(esa)], ['4'])).
% 0.25/0.47  thf(t1_xboole_1, axiom,
% 0.25/0.47    (![A:$i,B:$i,C:$i]:
% 0.25/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.25/0.47       ( r1_tarski @ A @ C ) ))).
% 0.25/0.47  thf('6', plain,
% 0.25/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.47         (~ (r1_tarski @ X3 @ X4)
% 0.25/0.47          | ~ (r1_tarski @ X4 @ X5)
% 0.25/0.47          | (r1_tarski @ X3 @ X5))),
% 0.25/0.47      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.25/0.47  thf('7', plain,
% 0.25/0.47      ((![X0 : $i]:
% 0.25/0.47          ((r1_tarski @ sk_A @ X0)
% 0.25/0.47           | ~ (r1_tarski @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)) @ X0)))
% 0.25/0.47         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.25/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.25/0.47  thf('8', plain,
% 0.25/0.47      (((~ (v1_relat_1 @ sk_B) | (r1_tarski @ sk_A @ sk_B)))
% 0.25/0.47         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.25/0.47      inference('sup-', [status(thm)], ['3', '7'])).
% 0.25/0.47  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.47  thf('10', plain,
% 0.25/0.47      (((r1_tarski @ sk_A @ sk_B))
% 0.25/0.47         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.25/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.25/0.47  thf('11', plain,
% 0.25/0.47      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.25/0.47      inference('split', [status(esa)], ['0'])).
% 0.25/0.47  thf('12', plain,
% 0.25/0.47      (((r1_tarski @ sk_A @ sk_B)) | 
% 0.25/0.47       ~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.25/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.47  thf('13', plain,
% 0.25/0.47      (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.25/0.47      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.25/0.47  thf('14', plain,
% 0.25/0.47      (~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.25/0.47      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.25/0.47  thf('15', plain,
% 0.25/0.47      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_tarski @ sk_A @ sk_B)))),
% 0.25/0.47      inference('split', [status(esa)], ['4'])).
% 0.25/0.47  thf('16', plain,
% 0.25/0.47      (((r1_tarski @ sk_A @ sk_B)) | 
% 0.25/0.47       ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.25/0.47      inference('split', [status(esa)], ['4'])).
% 0.25/0.47  thf('17', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.25/0.47      inference('sat_resolution*', [status(thm)], ['2', '12', '16'])).
% 0.25/0.47  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.25/0.47      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 0.25/0.47  thf(d10_xboole_0, axiom,
% 0.25/0.47    (![A:$i,B:$i]:
% 0.25/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.25/0.47  thf('19', plain,
% 0.25/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.25/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.25/0.47  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.25/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.25/0.47  thf(d18_relat_1, axiom,
% 0.25/0.47    (![A:$i,B:$i]:
% 0.25/0.47     ( ( v1_relat_1 @ B ) =>
% 0.25/0.47       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.25/0.47  thf('21', plain,
% 0.25/0.47      (![X6 : $i, X7 : $i]:
% 0.25/0.47         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.25/0.47          | (v4_relat_1 @ X6 @ X7)
% 0.25/0.47          | ~ (v1_relat_1 @ X6))),
% 0.25/0.47      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.25/0.47  thf('22', plain,
% 0.25/0.47      (![X0 : $i]:
% 0.25/0.47         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.25/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.25/0.47  thf(t210_relat_1, axiom,
% 0.25/0.47    (![A:$i,B:$i]:
% 0.25/0.47     ( ( v1_relat_1 @ B ) =>
% 0.25/0.47       ( ![C:$i]:
% 0.25/0.47         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.25/0.47           ( ( r1_tarski @ C @ B ) =>
% 0.25/0.47             ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.25/0.47  thf('23', plain,
% 0.25/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.47         (~ (v1_relat_1 @ X8)
% 0.25/0.47          | ~ (v4_relat_1 @ X8 @ X9)
% 0.25/0.47          | (r1_tarski @ X8 @ (k7_relat_1 @ X10 @ X9))
% 0.25/0.47          | ~ (r1_tarski @ X8 @ X10)
% 0.25/0.47          | ~ (v1_relat_1 @ X10))),
% 0.25/0.47      inference('cnf', [status(esa)], [t210_relat_1])).
% 0.25/0.47  thf('24', plain,
% 0.25/0.47      (![X0 : $i, X1 : $i]:
% 0.25/0.47         (~ (v1_relat_1 @ X0)
% 0.25/0.47          | ~ (v1_relat_1 @ X1)
% 0.25/0.47          | ~ (r1_tarski @ X0 @ X1)
% 0.25/0.47          | (r1_tarski @ X0 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.25/0.47          | ~ (v1_relat_1 @ X0))),
% 0.25/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.25/0.47  thf('25', plain,
% 0.25/0.47      (![X0 : $i, X1 : $i]:
% 0.25/0.47         ((r1_tarski @ X0 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.25/0.47          | ~ (r1_tarski @ X0 @ X1)
% 0.25/0.47          | ~ (v1_relat_1 @ X1)
% 0.25/0.47          | ~ (v1_relat_1 @ X0))),
% 0.25/0.47      inference('simplify', [status(thm)], ['24'])).
% 0.25/0.47  thf('26', plain,
% 0.25/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.25/0.47        | ~ (v1_relat_1 @ sk_B)
% 0.25/0.47        | (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.25/0.47      inference('sup-', [status(thm)], ['18', '25'])).
% 0.25/0.47  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.25/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.47  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.47  thf('29', plain,
% 0.25/0.47      ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.25/0.47      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.25/0.47  thf('30', plain, ($false), inference('demod', [status(thm)], ['14', '29'])).
% 0.25/0.47  
% 0.25/0.47  % SZS output end Refutation
% 0.25/0.47  
% 0.25/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
