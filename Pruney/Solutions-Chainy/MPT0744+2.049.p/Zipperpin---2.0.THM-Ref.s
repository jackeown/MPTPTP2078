%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BeALgB21uG

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:06 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 123 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  569 (1003 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X14 @ X15 )
      | ( r1_ordinal1 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X14 @ X15 )
      | ( r1_ordinal1 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( r1_ordinal1 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('42',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('48',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_ordinal1 @ X21 ) )
      | ( X20 != X21 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('58',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_ordinal1 @ X21 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','58'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','32','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BeALgB21uG
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 250 iterations in 0.114s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.37/0.58  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(t34_ordinal1, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.58           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.58             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( v3_ordinal1 @ A ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( v3_ordinal1 @ B ) =>
% 0.37/0.58              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.58                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.37/0.58        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.58       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.58      inference('split', [status(esa)], ['0'])).
% 0.37/0.58  thf(connectedness_r1_ordinal1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.58       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i]:
% 0.37/0.58         (~ (v3_ordinal1 @ X14)
% 0.37/0.58          | ~ (v3_ordinal1 @ X15)
% 0.37/0.58          | (r1_ordinal1 @ X14 @ X15)
% 0.37/0.58          | (r1_ordinal1 @ X15 @ X14))),
% 0.37/0.58      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.37/0.58      inference('eq_fact', [status(thm)], ['2'])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['3'])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i]:
% 0.37/0.58         (~ (v3_ordinal1 @ X14)
% 0.37/0.58          | ~ (v3_ordinal1 @ X15)
% 0.37/0.58          | (r1_ordinal1 @ X14 @ X15)
% 0.37/0.58          | (r1_ordinal1 @ X15 @ X14))),
% 0.37/0.58      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.37/0.58  thf(redefinition_r1_ordinal1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.58       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X17 : $i, X18 : $i]:
% 0.37/0.58         (~ (v3_ordinal1 @ X17)
% 0.37/0.58          | ~ (v3_ordinal1 @ X18)
% 0.37/0.58          | (r1_tarski @ X17 @ X18)
% 0.37/0.58          | ~ (r1_ordinal1 @ X17 @ X18))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_ordinal1 @ X0 @ X1)
% 0.37/0.58          | ~ (v3_ordinal1 @ X0)
% 0.37/0.58          | ~ (v3_ordinal1 @ X1)
% 0.37/0.58          | (r1_tarski @ X1 @ X0)
% 0.37/0.58          | ~ (v3_ordinal1 @ X0)
% 0.37/0.58          | ~ (v3_ordinal1 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_tarski @ X1 @ X0)
% 0.37/0.58          | ~ (v3_ordinal1 @ X1)
% 0.37/0.58          | ~ (v3_ordinal1 @ X0)
% 0.37/0.58          | (r1_ordinal1 @ X0 @ X1))),
% 0.37/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('split', [status(esa)], ['0'])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (((~ (v3_ordinal1 @ sk_A)
% 0.37/0.58         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.58         | (r1_tarski @ sk_B @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.58         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('split', [status(esa)], ['14'])).
% 0.37/0.58  thf(d1_ordinal1, axiom,
% 0.37/0.58    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X16 : $i]:
% 0.37/0.58         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.37/0.58  thf(d3_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.58       ( ![D:$i]:
% 0.37/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.58           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.58          | (r2_hidden @ X4 @ X3)
% 0.37/0.58          | (r2_hidden @ X4 @ X1)
% 0.37/0.58          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.37/0.58         ((r2_hidden @ X4 @ X1)
% 0.37/0.58          | (r2_hidden @ X4 @ X3)
% 0.37/0.58          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.37/0.58          | (r2_hidden @ X1 @ X0)
% 0.37/0.58          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '18'])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.58         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['15', '19'])).
% 0.37/0.58  thf(d1_tarski, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X12 @ X11)
% 0.37/0.58          | ((X12) = (X9))
% 0.37/0.58          | ((X11) != (k1_tarski @ X9)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X9 : $i, X12 : $i]:
% 0.37/0.58         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.37/0.58         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['20', '22'])).
% 0.37/0.58  thf(t7_ordinal1, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X24 : $i, X25 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.37/0.58         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      ((((sk_A) = (sk_B)))
% 0.37/0.58         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.37/0.58             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['13', '25'])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('split', [status(esa)], ['0'])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.37/0.58         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.37/0.58             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      ((~ (v3_ordinal1 @ sk_A))
% 0.37/0.58         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.37/0.58             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['4', '28'])).
% 0.37/0.58  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.58       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.58       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.58      inference('split', [status(esa)], ['14'])).
% 0.37/0.58  thf(t26_ordinal1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.58           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X22 : $i, X23 : $i]:
% 0.37/0.58         (~ (v3_ordinal1 @ X22)
% 0.37/0.58          | (r1_ordinal1 @ X23 @ X22)
% 0.37/0.58          | (r2_hidden @ X22 @ X23)
% 0.37/0.58          | ~ (v3_ordinal1 @ X23))),
% 0.37/0.58      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.58  thf(t13_ordinal1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.58       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X20 : $i, X21 : $i]:
% 0.37/0.58         ((r2_hidden @ X20 @ (k1_ordinal1 @ X21)) | ~ (r2_hidden @ X20 @ X21))),
% 0.37/0.58      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v3_ordinal1 @ X0)
% 0.37/0.58          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.58          | ~ (v3_ordinal1 @ X1)
% 0.37/0.58          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.58         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('split', [status(esa)], ['0'])).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (((~ (v3_ordinal1 @ sk_A)
% 0.37/0.58         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.37/0.58         | ~ (v3_ordinal1 @ sk_B)))
% 0.37/0.58         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.58  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('39', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.37/0.58         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      (![X17 : $i, X18 : $i]:
% 0.37/0.58         (~ (v3_ordinal1 @ X17)
% 0.37/0.58          | ~ (v3_ordinal1 @ X18)
% 0.37/0.58          | (r1_tarski @ X17 @ X18)
% 0.37/0.58          | ~ (r1_ordinal1 @ X17 @ X18))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      ((((r1_tarski @ sk_B @ sk_A)
% 0.37/0.58         | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.58         | ~ (v3_ordinal1 @ sk_B)))
% 0.37/0.58         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.58  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      (((r1_tarski @ sk_B @ sk_A))
% 0.37/0.58         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('split', [status(esa)], ['14'])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (![X17 : $i, X18 : $i]:
% 0.37/0.58         (~ (v3_ordinal1 @ X17)
% 0.37/0.58          | ~ (v3_ordinal1 @ X18)
% 0.37/0.58          | (r1_tarski @ X17 @ X18)
% 0.37/0.58          | ~ (r1_ordinal1 @ X17 @ X18))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      ((((r1_tarski @ sk_A @ sk_B)
% 0.37/0.58         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.58         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.58  thf('49', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.37/0.58  thf(d10_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      (![X6 : $i, X8 : $i]:
% 0.37/0.58         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.37/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 0.37/0.58         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      ((((sk_B) = (sk_A)))
% 0.37/0.58         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.37/0.58             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['45', '53'])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.58         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.58      inference('split', [status(esa)], ['0'])).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.37/0.58         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.37/0.58             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.58  thf('57', plain,
% 0.37/0.58      (![X20 : $i, X21 : $i]:
% 0.37/0.58         ((r2_hidden @ X20 @ (k1_ordinal1 @ X21)) | ((X20) != (X21)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.58  thf('58', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_ordinal1 @ X21))),
% 0.37/0.58      inference('simplify', [status(thm)], ['57'])).
% 0.37/0.58  thf('59', plain,
% 0.37/0.58      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.58       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['56', '58'])).
% 0.37/0.58  thf('60', plain, ($false),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['1', '31', '32', '59'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
