%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DVaW7XoViV

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:16 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   56 (  97 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   22
%              Number of atoms          :  496 ( 995 expanded)
%              Number of equality atoms :   33 (  59 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t50_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_xboole_0 @ A @ B )
              & ( A != B )
              & ~ ( r2_xboole_0 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ~ ( ~ ( r2_xboole_0 @ A @ B )
                & ( A != B )
                & ~ ( r2_xboole_0 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_ordinal1])).

thf('0',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( r2_hidden @ X21 @ X20 )
      | ( X21 = X20 )
      | ( r2_hidden @ X20 @ X21 )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v3_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X19 )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( r2_hidden @ X21 @ X20 )
      | ( X21 = X20 )
      | ( r2_hidden @ X20 @ X21 )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C @ X0 @ X1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ X0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X1 )
      | ( r2_hidden @ X1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_ordinal1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ B @ C )
        & ( r2_hidden @ C @ A ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_ordinal1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X2 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X0 = sk_A )
      | ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( X0 = sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = sk_A )
      | ( r2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( r2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('37',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_xboole_0 @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DVaW7XoViV
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 198 iterations in 0.145s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(t50_ordinal1, conjecture,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.40/0.61           ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.40/0.61                ( ~( r2_xboole_0 @ B @ A ) ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i]:
% 0.40/0.61        ( ( v3_ordinal1 @ A ) =>
% 0.40/0.61          ( ![B:$i]:
% 0.40/0.61            ( ( v3_ordinal1 @ B ) =>
% 0.40/0.61              ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.40/0.61                   ( ~( r2_xboole_0 @ B @ A ) ) ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t50_ordinal1])).
% 0.40/0.61  thf('0', plain, (~ (r2_xboole_0 @ sk_A @ sk_B_1)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('1', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(t24_ordinal1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.40/0.61           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.40/0.61                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X20 : $i, X21 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ X20)
% 0.40/0.61          | (r2_hidden @ X21 @ X20)
% 0.40/0.61          | ((X21) = (X20))
% 0.40/0.61          | (r2_hidden @ X20 @ X21)
% 0.40/0.61          | ~ (v3_ordinal1 @ X21))),
% 0.40/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.40/0.61  thf(d3_tarski, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X3 : $i, X5 : $i]:
% 0.40/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf(t23_ordinal1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X18 : $i, X19 : $i]:
% 0.40/0.61         ((v3_ordinal1 @ X18)
% 0.40/0.61          | ~ (v3_ordinal1 @ X19)
% 0.40/0.61          | ~ (r2_hidden @ X18 @ X19))),
% 0.40/0.61      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | (v3_ordinal1 @ (sk_C @ X1 @ X0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X20 : $i, X21 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ X20)
% 0.40/0.61          | (r2_hidden @ X21 @ X20)
% 0.40/0.61          | ((X21) = (X20))
% 0.40/0.61          | (r2_hidden @ X20 @ X21)
% 0.40/0.61          | ~ (v3_ordinal1 @ X21))),
% 0.40/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X3 : $i, X5 : $i]:
% 0.40/0.61         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ (sk_C @ X0 @ X1))
% 0.40/0.61          | (r2_hidden @ X0 @ (sk_C @ X0 @ X1))
% 0.40/0.61          | ((sk_C @ X0 @ X1) = (X0))
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | (r1_tarski @ X1 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ X0)
% 0.40/0.61          | (r1_tarski @ X0 @ X1)
% 0.40/0.61          | (r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | ((sk_C @ X1 @ X0) = (X1))
% 0.40/0.61          | (r2_hidden @ X1 @ (sk_C @ X1 @ X0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r2_hidden @ X1 @ (sk_C @ X1 @ X0))
% 0.40/0.61          | ((sk_C @ X1 @ X0) = (X1))
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['9'])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X3 : $i, X5 : $i]:
% 0.40/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf(t3_ordinal1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ~( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) & ( r2_hidden @ C @ A ) ) ))).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X22 @ X23)
% 0.40/0.61          | ~ (r2_hidden @ X24 @ X22)
% 0.40/0.61          | ~ (r2_hidden @ X23 @ X24))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_ordinal1])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (r2_hidden @ X0 @ X2)
% 0.40/0.61          | ~ (r2_hidden @ X2 @ (sk_C @ X1 @ X0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ X0)
% 0.40/0.61          | (r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | ((sk_C @ X1 @ X0) = (X1))
% 0.40/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.40/0.61          | (r1_tarski @ X0 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['10', '13'])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.61          | ((sk_C @ X1 @ X0) = (X1))
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r2_hidden @ X0 @ X1)
% 0.40/0.61          | ((X1) = (X0))
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r1_tarski @ X1 @ X0)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((sk_C @ X0 @ X1) = (X0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['2', '15'])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((sk_C @ X0 @ X1) = (X0))
% 0.40/0.61          | (r1_tarski @ X1 @ X0)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X1) = (X0))
% 0.40/0.61          | (r2_hidden @ X0 @ X1)
% 0.40/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X3 : $i, X5 : $i]:
% 0.40/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r2_hidden @ X0 @ X1)
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r2_hidden @ X0 @ X1)
% 0.40/0.61          | ((X1) = (X0))
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | (r1_tarski @ X1 @ X0)
% 0.40/0.61          | (r1_tarski @ X1 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_tarski @ X1 @ X0)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X1) = (X0))
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r2_hidden @ X0 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_tarski @ X1 @ X0)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X1) = (X0))
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r2_hidden @ X0 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.61  thf(antisymmetry_r2_hidden, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.61      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X0) = (X1))
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X0) = (X1))
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | (r1_tarski @ X0 @ X1)
% 0.40/0.61          | (r1_tarski @ X1 @ X0)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X1) = (X0))
% 0.40/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['20', '23'])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_tarski @ X1 @ X0)
% 0.40/0.61          | (r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (v3_ordinal1 @ X1)
% 0.40/0.61          | ((X0) = (X1))
% 0.40/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X0) = (sk_A))
% 0.40/0.61          | (r1_tarski @ X0 @ sk_A)
% 0.40/0.61          | (r1_tarski @ sk_A @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '25'])).
% 0.40/0.61  thf(d8_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.40/0.61       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X6 : $i, X8 : $i]:
% 0.40/0.61         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.40/0.61      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((r1_tarski @ sk_A @ X0)
% 0.40/0.61          | ((X0) = (sk_A))
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X0) = (sk_A))
% 0.40/0.61          | (r2_xboole_0 @ X0 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((r2_xboole_0 @ X0 @ sk_A)
% 0.40/0.61          | ~ (v3_ordinal1 @ X0)
% 0.40/0.61          | ((X0) = (sk_A))
% 0.40/0.61          | (r1_tarski @ sk_A @ X0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.40/0.61  thf('30', plain, (~ (r2_xboole_0 @ sk_B_1 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (((r1_tarski @ sk_A @ sk_B_1)
% 0.40/0.61        | ((sk_B_1) = (sk_A))
% 0.40/0.61        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('32', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('33', plain, (((r1_tarski @ sk_A @ sk_B_1) | ((sk_B_1) = (sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.61  thf('34', plain, (((sk_A) != (sk_B_1))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('35', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      (![X6 : $i, X8 : $i]:
% 0.40/0.61         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.40/0.61      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.40/0.61  thf('37', plain, ((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.61  thf('38', plain, (((sk_A) != (sk_B_1))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('39', plain, ((r2_xboole_0 @ sk_A @ sk_B_1)),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.40/0.61  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
