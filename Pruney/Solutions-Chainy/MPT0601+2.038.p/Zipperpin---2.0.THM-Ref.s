%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2B7x0BGqON

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:46 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 112 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  385 ( 893 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('14',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ ( k11_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('17',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k11_relat_1 @ X12 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['9','24','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['26','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2B7x0BGqON
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 305 iterations in 0.234s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.47/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.69  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.69  thf(l13_xboole_0, axiom,
% 0.47/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.69      inference('sup+', [status(thm)], ['0', '1'])).
% 0.47/0.69  thf(t205_relat_1, conjecture,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ B ) =>
% 0.47/0.69       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.47/0.69         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i,B:$i]:
% 0.47/0.69        ( ( v1_relat_1 @ B ) =>
% 0.47/0.69          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.47/0.69            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.47/0.69        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('4', plain,
% 0.47/0.69      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.47/0.69         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('split', [status(esa)], ['3'])).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      ((![X0 : $i]:
% 0.47/0.69          (((X0) != (k1_xboole_0))
% 0.47/0.69           | ~ (v1_xboole_0 @ X0)
% 0.47/0.69           | ~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.47/0.69         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['2', '4'])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))
% 0.47/0.69         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.69         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.69  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.47/0.69         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('simplify_reflect+', [status(thm)], ['6', '7'])).
% 0.47/0.69  thf('9', plain,
% 0.47/0.69      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.47/0.69       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.47/0.69      inference('split', [status(esa)], ['3'])).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.47/0.69        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.47/0.69         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('split', [status(esa)], ['10'])).
% 0.47/0.69  thf('12', plain,
% 0.47/0.69      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.47/0.69         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.47/0.69      inference('split', [status(esa)], ['3'])).
% 0.47/0.69  thf(d4_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.47/0.69       ( ![C:$i]:
% 0.47/0.69         ( ( r2_hidden @ C @ B ) <=>
% 0.47/0.69           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.47/0.69  thf('13', plain,
% 0.47/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X8 @ X7)
% 0.47/0.69          | (r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 0.47/0.69          | ((X7) != (k1_relat_1 @ X6)))),
% 0.47/0.69      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X6 : $i, X8 : $i]:
% 0.47/0.69         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 0.47/0.69          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['13'])).
% 0.47/0.69  thf('15', plain,
% 0.47/0.69      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.47/0.69         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['12', '14'])).
% 0.47/0.69  thf(t204_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ C ) =>
% 0.47/0.69       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.47/0.69         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.69         (~ (r2_hidden @ (k4_tarski @ X13 @ X11) @ X12)
% 0.47/0.69          | (r2_hidden @ X11 @ (k11_relat_1 @ X12 @ X13))
% 0.47/0.69          | ~ (v1_relat_1 @ X12))),
% 0.47/0.69      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (((~ (v1_relat_1 @ sk_B_1)
% 0.47/0.69         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.69            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.47/0.69         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('18', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.47/0.69         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.47/0.69      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.69  thf(d1_xboole_0, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.69  thf('20', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.47/0.69         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.47/0.69         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.47/0.69             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['11', '21'])).
% 0.47/0.69  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.47/0.69       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.69  thf('25', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.69      inference('sat_resolution*', [status(thm)], ['9', '24'])).
% 0.47/0.69  thf('26', plain, (~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['8', '25'])).
% 0.47/0.69  thf('27', plain,
% 0.47/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.69  thf('28', plain,
% 0.47/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X11 @ (k11_relat_1 @ X12 @ X13))
% 0.47/0.69          | (r2_hidden @ (k4_tarski @ X13 @ X11) @ X12)
% 0.47/0.69          | ~ (v1_relat_1 @ X12))),
% 0.47/0.69      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((v1_xboole_0 @ (k11_relat_1 @ X1 @ X0))
% 0.47/0.69          | ~ (v1_relat_1 @ X1)
% 0.47/0.69          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.47/0.69             X1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.69         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.47/0.69          | (r2_hidden @ X4 @ X7)
% 0.47/0.69          | ((X7) != (k1_relat_1 @ X6)))),
% 0.47/0.69      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.69         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 0.47/0.69          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.47/0.69      inference('simplify', [status(thm)], ['30'])).
% 0.47/0.69  thf('32', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ X0)
% 0.47/0.69          | (v1_xboole_0 @ (k11_relat_1 @ X0 @ X1))
% 0.47/0.69          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['29', '31'])).
% 0.47/0.69  thf('33', plain,
% 0.47/0.69      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.47/0.69         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.47/0.69      inference('split', [status(esa)], ['10'])).
% 0.47/0.69  thf('34', plain,
% 0.47/0.69      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.47/0.69       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.69      inference('split', [status(esa)], ['10'])).
% 0.47/0.69  thf('35', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.47/0.69      inference('sat_resolution*', [status(thm)], ['9', '24', '34'])).
% 0.47/0.69  thf('36', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 0.47/0.69  thf('37', plain,
% 0.47/0.69      (((v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)) | ~ (v1_relat_1 @ sk_B_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['32', '36'])).
% 0.47/0.69  thf('38', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('39', plain, ((v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))),
% 0.47/0.69      inference('demod', [status(thm)], ['37', '38'])).
% 0.47/0.69  thf('40', plain, ($false), inference('demod', [status(thm)], ['26', '39'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.55/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
