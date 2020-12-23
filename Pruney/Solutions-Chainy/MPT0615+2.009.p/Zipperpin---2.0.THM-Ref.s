%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j3o2arjDdn

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:17 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  83 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  278 ( 758 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf(t186_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
              & ( r1_tarski @ C @ B ) )
           => ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( r1_tarski @ X6 @ ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t186_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['14','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j3o2arjDdn
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.43  % Solved by: fo/fo7.sh
% 0.19/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.43  % done 44 iterations in 0.014s
% 0.19/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.43  % SZS output start Refutation
% 0.19/0.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.43  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.43  thf(t219_relat_1, conjecture,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( v1_relat_1 @ A ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( v1_relat_1 @ B ) =>
% 0.19/0.43           ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.43             ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ))).
% 0.19/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.43    (~( ![A:$i]:
% 0.19/0.43        ( ( v1_relat_1 @ A ) =>
% 0.19/0.43          ( ![B:$i]:
% 0.19/0.43            ( ( v1_relat_1 @ B ) =>
% 0.19/0.43              ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.43                ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )),
% 0.19/0.43    inference('cnf.neg', [status(esa)], [t219_relat_1])).
% 0.19/0.43  thf('0', plain,
% 0.19/0.43      ((~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.19/0.43        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('1', plain,
% 0.19/0.43      ((~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.19/0.43         <= (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.19/0.43      inference('split', [status(esa)], ['0'])).
% 0.19/0.43  thf('2', plain,
% 0.19/0.43      (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))) | 
% 0.19/0.43       ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.19/0.43      inference('split', [status(esa)], ['0'])).
% 0.19/0.43  thf(t88_relat_1, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.19/0.43  thf('3', plain,
% 0.19/0.43      (![X9 : $i, X10 : $i]:
% 0.19/0.43         ((r1_tarski @ (k7_relat_1 @ X9 @ X10) @ X9) | ~ (v1_relat_1 @ X9))),
% 0.19/0.43      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.19/0.43  thf('4', plain,
% 0.19/0.43      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.19/0.43        | (r1_tarski @ sk_A @ sk_B))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('5', plain,
% 0.19/0.43      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.19/0.43         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.19/0.43      inference('split', [status(esa)], ['4'])).
% 0.19/0.43  thf(t1_xboole_1, axiom,
% 0.19/0.43    (![A:$i,B:$i,C:$i]:
% 0.19/0.43     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.43       ( r1_tarski @ A @ C ) ))).
% 0.19/0.43  thf('6', plain,
% 0.19/0.43      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.43         (~ (r1_tarski @ X3 @ X4)
% 0.19/0.43          | ~ (r1_tarski @ X4 @ X5)
% 0.19/0.43          | (r1_tarski @ X3 @ X5))),
% 0.19/0.43      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.43  thf('7', plain,
% 0.19/0.43      ((![X0 : $i]:
% 0.19/0.43          ((r1_tarski @ sk_A @ X0)
% 0.19/0.43           | ~ (r1_tarski @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)) @ X0)))
% 0.19/0.43         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.19/0.43      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.43  thf('8', plain,
% 0.19/0.43      (((~ (v1_relat_1 @ sk_B) | (r1_tarski @ sk_A @ sk_B)))
% 0.19/0.43         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.19/0.43      inference('sup-', [status(thm)], ['3', '7'])).
% 0.19/0.43  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('10', plain,
% 0.19/0.43      (((r1_tarski @ sk_A @ sk_B))
% 0.19/0.43         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.19/0.43      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.43  thf('11', plain,
% 0.19/0.43      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.19/0.43      inference('split', [status(esa)], ['0'])).
% 0.19/0.43  thf('12', plain,
% 0.19/0.43      (((r1_tarski @ sk_A @ sk_B)) | 
% 0.19/0.43       ~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.19/0.43      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.43  thf('13', plain,
% 0.19/0.43      (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.19/0.43      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.19/0.43  thf('14', plain,
% 0.19/0.43      (~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.19/0.43      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.19/0.43  thf('15', plain,
% 0.19/0.43      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_tarski @ sk_A @ sk_B)))),
% 0.19/0.43      inference('split', [status(esa)], ['4'])).
% 0.19/0.43  thf('16', plain,
% 0.19/0.43      (((r1_tarski @ sk_A @ sk_B)) | 
% 0.19/0.43       ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.19/0.43      inference('split', [status(esa)], ['4'])).
% 0.19/0.43  thf('17', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.19/0.43      inference('sat_resolution*', [status(thm)], ['2', '12', '16'])).
% 0.19/0.43  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.43      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 0.19/0.43  thf(d10_xboole_0, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.43  thf('19', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.43  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.43      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.43  thf(t186_relat_1, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ( v1_relat_1 @ B ) =>
% 0.19/0.43       ( ![C:$i]:
% 0.19/0.43         ( ( v1_relat_1 @ C ) =>
% 0.19/0.43           ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.19/0.43             ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.19/0.43  thf('21', plain,
% 0.19/0.43      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.43         (~ (v1_relat_1 @ X6)
% 0.19/0.43          | (r1_tarski @ X6 @ (k7_relat_1 @ X7 @ X8))
% 0.19/0.43          | ~ (r1_tarski @ X6 @ X7)
% 0.19/0.43          | ~ (r1_tarski @ (k1_relat_1 @ X6) @ X8)
% 0.19/0.43          | ~ (v1_relat_1 @ X7))),
% 0.19/0.43      inference('cnf', [status(esa)], [t186_relat_1])).
% 0.19/0.43  thf('22', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i]:
% 0.19/0.43         (~ (v1_relat_1 @ X1)
% 0.19/0.43          | ~ (r1_tarski @ X0 @ X1)
% 0.19/0.43          | (r1_tarski @ X0 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.19/0.43          | ~ (v1_relat_1 @ X0))),
% 0.19/0.43      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.43  thf('23', plain,
% 0.19/0.43      ((~ (v1_relat_1 @ sk_A)
% 0.19/0.43        | (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.19/0.43        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.43      inference('sup-', [status(thm)], ['18', '22'])).
% 0.19/0.43  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('26', plain,
% 0.19/0.43      ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.19/0.43      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.43  thf('27', plain, ($false), inference('demod', [status(thm)], ['14', '26'])).
% 0.19/0.43  
% 0.19/0.43  % SZS output end Refutation
% 0.19/0.43  
% 0.19/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
