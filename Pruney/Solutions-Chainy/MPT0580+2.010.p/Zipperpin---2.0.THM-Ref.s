%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y1lu0Nu0mf

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  87 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  431 ( 710 expanded)
%              Number of equality atoms :   39 (  65 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v3_relat_1_type,type,(
    v3_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t184_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v3_relat_1 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v3_relat_1 @ A )
        <=> ! [B: $i] :
              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t184_relat_1])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X12: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) )
      | ( X12 = k1_xboole_0 )
      | ( v3_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v3_relat_1 @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( ~ ( v3_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v3_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v3_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v3_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( X8 = X7 )
      | ( X8 = X4 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ( X8 = X4 )
      | ( X8 = X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('26',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) )
          = k1_xboole_0 ) )
   <= ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) )
   <= ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) )
   <= ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
   <= ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
   <= ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v3_relat_1 @ sk_A ) )
   <= ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ! [X12: $i] :
        ( ( X12 = k1_xboole_0 )
        | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v3_relat_1 @ sk_A )
   <= ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ~ ! [X12: $i] :
          ( ( X12 = k1_xboole_0 )
          | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','22','23','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y1lu0Nu0mf
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:01:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 78 iterations in 0.040s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(v3_relat_1_type, type, v3_relat_1: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(t184_relat_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( v3_relat_1 @ A ) <=>
% 0.21/0.48         ( ![B:$i]:
% 0.21/0.48           ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.21/0.48             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ A ) =>
% 0.21/0.48          ( ( v3_relat_1 @ A ) <=>
% 0.21/0.48            ( ![B:$i]:
% 0.21/0.48              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.21/0.48                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t184_relat_1])).
% 0.21/0.48  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain, (~ (((sk_B) = (k1_xboole_0))) | ~ ((v3_relat_1 @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)) | ~ (v3_relat_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | ~ ((v3_relat_1 @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X12 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A))
% 0.21/0.48          | ((X12) = (k1_xboole_0))
% 0.21/0.48          | (v3_relat_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, (((v3_relat_1 @ sk_A)) <= (((v3_relat_1 @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.21/0.48         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf(d15_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( v3_relat_1 @ A ) <=>
% 0.21/0.48         ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (~ (v3_relat_1 @ X11)
% 0.21/0.48          | (r1_tarski @ (k2_relat_1 @ X11) @ (k1_tarski @ k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.48          | (r2_hidden @ X0 @ X2)
% 0.21/0.48          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v3_relat_1 @ X0)
% 0.21/0.48          | (r2_hidden @ X1 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.48         | ~ (v3_relat_1 @ sk_A)
% 0.21/0.48         | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.48         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.48  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)) | ~ (v3_relat_1 @ sk_A)))
% 0.21/0.48         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)))
% 0.21/0.48         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '12'])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(d2_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.48          | ((X8) = (X7))
% 0.21/0.48          | ((X8) = (X4))
% 0.21/0.48          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X4 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (((X8) = (X4))
% 0.21/0.48          | ((X8) = (X7))
% 0.21/0.48          | ~ (r2_hidden @ X8 @ (k2_tarski @ X7 @ X4)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.48         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((((sk_B) != (sk_B)))
% 0.21/0.48         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.21/0.48             ((v3_relat_1 @ sk_A)) & 
% 0.21/0.48             ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | 
% 0.21/0.48       ~ ((v3_relat_1 @ sk_A)) | (((sk_B) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((![X12 : $i]:
% 0.21/0.48          (((X12) = (k1_xboole_0)) | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))) | 
% 0.21/0.48       ((v3_relat_1 @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['4'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (((X5) != (X4))
% 0.21/0.49          | (r2_hidden @ X5 @ X6)
% 0.21/0.49          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.21/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((![X12 : $i]:
% 0.21/0.49          (((X12) = (k1_xboole_0)) | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A))))
% 0.21/0.49         <= ((![X12 : $i]:
% 0.21/0.49                (((X12) = (k1_xboole_0))
% 0.21/0.49                 | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.49      inference('split', [status(esa)], ['4'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.21/0.49           | ((sk_C @ X0 @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))))
% 0.21/0.49         <= ((![X12 : $i]:
% 0.21/0.49                (((X12) = (k1_xboole_0))
% 0.21/0.49                 | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.21/0.49           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.21/0.49           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)))
% 0.21/0.49         <= ((![X12 : $i]:
% 0.21/0.49                (((X12) = (k1_xboole_0))
% 0.21/0.49                 | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.21/0.49           | ~ (r2_hidden @ k1_xboole_0 @ X0)))
% 0.21/0.49         <= ((![X12 : $i]:
% 0.21/0.49                (((X12) = (k1_xboole_0))
% 0.21/0.49                 | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_tarski @ X0 @ k1_xboole_0)))
% 0.21/0.49         <= ((![X12 : $i]:
% 0.21/0.49                (((X12) = (k1_xboole_0))
% 0.21/0.49                 | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_tarski @ k1_xboole_0)))
% 0.21/0.49         <= ((![X12 : $i]:
% 0.21/0.49                (((X12) = (k1_xboole_0))
% 0.21/0.49                 | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['24', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X11) @ (k1_tarski @ k1_xboole_0))
% 0.21/0.49          | (v3_relat_1 @ X11)
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((~ (v1_relat_1 @ sk_A) | (v3_relat_1 @ sk_A)))
% 0.21/0.49         <= ((![X12 : $i]:
% 0.21/0.49                (((X12) = (k1_xboole_0))
% 0.21/0.49                 | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (((v3_relat_1 @ sk_A))
% 0.21/0.49         <= ((![X12 : $i]:
% 0.21/0.49                (((X12) = (k1_xboole_0))
% 0.21/0.49                 | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((~ (v3_relat_1 @ sk_A)) <= (~ ((v3_relat_1 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (~
% 0.21/0.49       (![X12 : $i]:
% 0.21/0.49          (((X12) = (k1_xboole_0)) | ~ (r2_hidden @ X12 @ (k2_relat_1 @ sk_A)))) | 
% 0.21/0.49       ((v3_relat_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['1', '3', '22', '23', '40'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
