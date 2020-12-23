%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wa0RpCX4AY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:57 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  422 ( 572 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) ) @ X8 )
      | ( r1_tarski @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k1_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t77_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
         => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_relat_1])).

thf('4',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) ) @ X8 )
      | ( r1_tarski @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t74_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_D @ X0 @ sk_B ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_D @ X0 @ sk_B ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_D @ X0 @ sk_B ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) ) @ X7 )
      | ( r1_tarski @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X23 ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( sk_B
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wa0RpCX4AY
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:36:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 161 iterations in 0.184s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.39/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.39/0.61  thf(d3_relat_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.61           ( ![C:$i,D:$i]:
% 0.39/0.61             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.39/0.61               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X7 @ X8) @ (sk_D @ X7 @ X8)) @ X8)
% 0.39/0.61          | (r1_tarski @ X8 @ X7)
% 0.39/0.61          | ~ (v1_relat_1 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.39/0.61  thf(d4_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.39/0.61       ( ![C:$i]:
% 0.39/0.61         ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.61           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.61         (~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14)
% 0.39/0.61          | (r2_hidden @ X12 @ X15)
% 0.39/0.61          | ((X15) != (k1_relat_1 @ X14)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.61         ((r2_hidden @ X12 @ (k1_relat_1 @ X14))
% 0.39/0.61          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14))),
% 0.39/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X0)
% 0.39/0.61          | (r1_tarski @ X0 @ X1)
% 0.39/0.61          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['0', '2'])).
% 0.39/0.61  thf(t77_relat_1, conjecture,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.39/0.61         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i]:
% 0.39/0.61        ( ( v1_relat_1 @ B ) =>
% 0.39/0.61          ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.39/0.61            ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t77_relat_1])).
% 0.39/0.61  thf('4', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d3_tarski, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.61          | (r2_hidden @ X0 @ X2)
% 0.39/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r1_tarski @ sk_B @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.39/0.61          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['3', '6'])).
% 0.39/0.61  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X7 @ X8) @ (sk_D @ X7 @ X8)) @ X8)
% 0.39/0.61          | (r1_tarski @ X8 @ X7)
% 0.39/0.61          | ~ (v1_relat_1 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.39/0.61  thf(t74_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ D ) =>
% 0.39/0.61       ( ( r2_hidden @
% 0.39/0.61           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) ) <=>
% 0.39/0.61         ( ( r2_hidden @ A @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X19 @ X20)
% 0.39/0.61          | ~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X22)
% 0.39/0.61          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ 
% 0.39/0.61             (k5_relat_1 @ (k6_relat_1 @ X20) @ X22))
% 0.39/0.61          | ~ (v1_relat_1 @ X22))),
% 0.39/0.61      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X0)
% 0.39/0.61          | (r1_tarski @ X0 @ X1)
% 0.39/0.61          | ~ (v1_relat_1 @ X0)
% 0.39/0.61          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ 
% 0.39/0.61             (k5_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 0.39/0.61          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.39/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2)
% 0.39/0.61          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ 
% 0.39/0.61             (k5_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 0.39/0.61          | (r1_tarski @ X0 @ X1)
% 0.39/0.61          | ~ (v1_relat_1 @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r1_tarski @ sk_B @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.39/0.61          | (r1_tarski @ sk_B @ X0)
% 0.39/0.61          | (r2_hidden @ 
% 0.39/0.61             (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ (sk_D @ X0 @ sk_B)) @ 
% 0.39/0.61             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['9', '13'])).
% 0.39/0.61  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r1_tarski @ sk_B @ X0)
% 0.39/0.61          | (r1_tarski @ sk_B @ X0)
% 0.39/0.61          | (r2_hidden @ 
% 0.39/0.61             (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ (sk_D @ X0 @ sk_B)) @ 
% 0.39/0.61             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r2_hidden @ 
% 0.39/0.61           (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ (sk_D @ X0 @ sk_B)) @ 
% 0.39/0.61           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.39/0.61          | (r1_tarski @ sk_B @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X7 @ X8) @ (sk_D @ X7 @ X8)) @ 
% 0.39/0.61             X7)
% 0.39/0.61          | (r1_tarski @ X8 @ X7)
% 0.39/0.61          | ~ (v1_relat_1 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (((r1_tarski @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.39/0.61        | ~ (v1_relat_1 @ sk_B)
% 0.39/0.61        | (r1_tarski @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.61  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (((r1_tarski @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.39/0.61        | (r1_tarski @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      ((r1_tarski @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.39/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.61  thf(t76_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.39/0.61         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (![X23 : $i, X24 : $i]:
% 0.39/0.61         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X24) @ X23) @ X23)
% 0.39/0.61          | ~ (v1_relat_1 @ X23))),
% 0.39/0.61      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.39/0.61  thf(d10_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X4 : $i, X6 : $i]:
% 0.39/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X0)
% 0.39/0.61          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.39/0.61          | ((X0) = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      ((((sk_B) = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.39/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['22', '25'])).
% 0.39/0.61  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('28', plain, (((sk_B) = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.39/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.61  thf('29', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('30', plain, ($false),
% 0.39/0.61      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
