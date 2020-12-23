%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VlF2G7Gt9h

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:56 EST 2020

% Result     : Theorem 6.31s
% Output     : Refutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 196 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  547 (1542 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('0',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( r2_hidden @ X23 @ ( k1_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('7',plain,(
    ! [X26: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('8',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_ordinal1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('10',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X26: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X25 @ X24 )
      | ( r2_hidden @ X24 @ X25 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k1_ordinal1 @ X20 )
      = ( k2_xboole_0 @ X20 @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('33',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('36',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','20'])).

thf('37',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,
    ( ( sk_B = sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X19 )
      | ( r1_ordinal1 @ X18 @ X19 )
      | ( r1_ordinal1 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_ordinal1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','22'])).

thf('49',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_ordinal1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('54',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['43','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['23','58','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VlF2G7Gt9h
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:34:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.31/6.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.31/6.49  % Solved by: fo/fo7.sh
% 6.31/6.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.31/6.49  % done 7316 iterations in 6.033s
% 6.31/6.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.31/6.49  % SZS output start Refutation
% 6.31/6.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.31/6.49  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 6.31/6.49  thf(sk_A_type, type, sk_A: $i).
% 6.31/6.49  thf(sk_B_type, type, sk_B: $i).
% 6.31/6.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.31/6.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.31/6.49  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 6.31/6.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.31/6.49  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 6.31/6.49  thf(t33_ordinal1, conjecture,
% 6.31/6.49    (![A:$i]:
% 6.31/6.49     ( ( v3_ordinal1 @ A ) =>
% 6.31/6.49       ( ![B:$i]:
% 6.31/6.49         ( ( v3_ordinal1 @ B ) =>
% 6.31/6.49           ( ( r2_hidden @ A @ B ) <=>
% 6.31/6.49             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 6.31/6.49  thf(zf_stmt_0, negated_conjecture,
% 6.31/6.49    (~( ![A:$i]:
% 6.31/6.49        ( ( v3_ordinal1 @ A ) =>
% 6.31/6.49          ( ![B:$i]:
% 6.31/6.49            ( ( v3_ordinal1 @ B ) =>
% 6.31/6.49              ( ( r2_hidden @ A @ B ) <=>
% 6.31/6.49                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 6.31/6.49    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 6.31/6.49  thf('0', plain,
% 6.31/6.49      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('1', plain,
% 6.31/6.49      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 6.31/6.49      inference('split', [status(esa)], ['0'])).
% 6.31/6.49  thf(t7_ordinal1, axiom,
% 6.31/6.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.31/6.49  thf('2', plain,
% 6.31/6.49      (![X27 : $i, X28 : $i]:
% 6.31/6.49         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 6.31/6.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 6.31/6.49  thf('3', plain,
% 6.31/6.49      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 6.31/6.49      inference('sup-', [status(thm)], ['1', '2'])).
% 6.31/6.49  thf('4', plain,
% 6.31/6.49      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 6.31/6.49        | ~ (r2_hidden @ sk_A @ sk_B))),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('5', plain,
% 6.31/6.49      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 6.31/6.49       ~ ((r2_hidden @ sk_A @ sk_B))),
% 6.31/6.49      inference('split', [status(esa)], ['4'])).
% 6.31/6.49  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 6.31/6.49  thf('6', plain, (![X23 : $i]: (r2_hidden @ X23 @ (k1_ordinal1 @ X23))),
% 6.31/6.49      inference('cnf', [status(esa)], [t10_ordinal1])).
% 6.31/6.49  thf(t29_ordinal1, axiom,
% 6.31/6.49    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 6.31/6.49  thf('7', plain,
% 6.31/6.49      (![X26 : $i]:
% 6.31/6.49         ((v3_ordinal1 @ (k1_ordinal1 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 6.31/6.49      inference('cnf', [status(esa)], [t29_ordinal1])).
% 6.31/6.49  thf('8', plain,
% 6.31/6.49      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 6.31/6.49         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 6.31/6.49      inference('split', [status(esa)], ['0'])).
% 6.31/6.49  thf(redefinition_r1_ordinal1, axiom,
% 6.31/6.49    (![A:$i,B:$i]:
% 6.31/6.49     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 6.31/6.49       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 6.31/6.49  thf('9', plain,
% 6.31/6.49      (![X21 : $i, X22 : $i]:
% 6.31/6.49         (~ (v3_ordinal1 @ X21)
% 6.31/6.49          | ~ (v3_ordinal1 @ X22)
% 6.31/6.49          | (r1_tarski @ X21 @ X22)
% 6.31/6.49          | ~ (r1_ordinal1 @ X21 @ X22))),
% 6.31/6.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 6.31/6.49  thf('10', plain,
% 6.31/6.49      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 6.31/6.49         | ~ (v3_ordinal1 @ sk_B)
% 6.31/6.49         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 6.31/6.49         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 6.31/6.49      inference('sup-', [status(thm)], ['8', '9'])).
% 6.31/6.49  thf('11', plain, ((v3_ordinal1 @ sk_B)),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('12', plain,
% 6.31/6.49      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 6.31/6.49         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 6.31/6.49         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 6.31/6.49      inference('demod', [status(thm)], ['10', '11'])).
% 6.31/6.49  thf('13', plain,
% 6.31/6.49      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 6.31/6.49         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 6.31/6.49      inference('sup-', [status(thm)], ['7', '12'])).
% 6.31/6.49  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('15', plain,
% 6.31/6.49      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 6.31/6.49         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 6.31/6.49      inference('demod', [status(thm)], ['13', '14'])).
% 6.31/6.49  thf(d3_tarski, axiom,
% 6.31/6.49    (![A:$i,B:$i]:
% 6.31/6.49     ( ( r1_tarski @ A @ B ) <=>
% 6.31/6.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.31/6.49  thf('16', plain,
% 6.31/6.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.31/6.49         (~ (r2_hidden @ X0 @ X1)
% 6.31/6.49          | (r2_hidden @ X0 @ X2)
% 6.31/6.49          | ~ (r1_tarski @ X1 @ X2))),
% 6.31/6.49      inference('cnf', [status(esa)], [d3_tarski])).
% 6.31/6.49  thf('17', plain,
% 6.31/6.49      ((![X0 : $i]:
% 6.31/6.49          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 6.31/6.49         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 6.31/6.49      inference('sup-', [status(thm)], ['15', '16'])).
% 6.31/6.49  thf('18', plain,
% 6.31/6.49      (((r2_hidden @ sk_A @ sk_B))
% 6.31/6.49         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 6.31/6.49      inference('sup-', [status(thm)], ['6', '17'])).
% 6.31/6.49  thf('19', plain,
% 6.31/6.49      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 6.31/6.49      inference('split', [status(esa)], ['4'])).
% 6.31/6.49  thf('20', plain,
% 6.31/6.49      (((r2_hidden @ sk_A @ sk_B)) | 
% 6.31/6.49       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 6.31/6.49      inference('sup-', [status(thm)], ['18', '19'])).
% 6.31/6.49  thf('21', plain,
% 6.31/6.49      (((r2_hidden @ sk_A @ sk_B)) | 
% 6.31/6.49       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 6.31/6.49      inference('split', [status(esa)], ['0'])).
% 6.31/6.49  thf('22', plain, (((r2_hidden @ sk_A @ sk_B))),
% 6.31/6.49      inference('sat_resolution*', [status(thm)], ['5', '20', '21'])).
% 6.31/6.49  thf('23', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 6.31/6.49      inference('simpl_trail', [status(thm)], ['3', '22'])).
% 6.31/6.49  thf('24', plain,
% 6.31/6.49      (![X26 : $i]:
% 6.31/6.49         ((v3_ordinal1 @ (k1_ordinal1 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 6.31/6.49      inference('cnf', [status(esa)], [t29_ordinal1])).
% 6.31/6.49  thf(t26_ordinal1, axiom,
% 6.31/6.49    (![A:$i]:
% 6.31/6.49     ( ( v3_ordinal1 @ A ) =>
% 6.31/6.49       ( ![B:$i]:
% 6.31/6.49         ( ( v3_ordinal1 @ B ) =>
% 6.31/6.49           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 6.31/6.49  thf('25', plain,
% 6.31/6.49      (![X24 : $i, X25 : $i]:
% 6.31/6.49         (~ (v3_ordinal1 @ X24)
% 6.31/6.49          | (r1_ordinal1 @ X25 @ X24)
% 6.31/6.49          | (r2_hidden @ X24 @ X25)
% 6.31/6.49          | ~ (v3_ordinal1 @ X25))),
% 6.31/6.49      inference('cnf', [status(esa)], [t26_ordinal1])).
% 6.31/6.49  thf(d1_ordinal1, axiom,
% 6.31/6.49    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 6.31/6.49  thf('26', plain,
% 6.31/6.49      (![X20 : $i]:
% 6.31/6.49         ((k1_ordinal1 @ X20) = (k2_xboole_0 @ X20 @ (k1_tarski @ X20)))),
% 6.31/6.49      inference('cnf', [status(esa)], [d1_ordinal1])).
% 6.31/6.49  thf(d3_xboole_0, axiom,
% 6.31/6.49    (![A:$i,B:$i,C:$i]:
% 6.31/6.49     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 6.31/6.49       ( ![D:$i]:
% 6.31/6.49         ( ( r2_hidden @ D @ C ) <=>
% 6.31/6.49           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 6.31/6.49  thf('27', plain,
% 6.31/6.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.31/6.49         (~ (r2_hidden @ X8 @ X6)
% 6.31/6.49          | (r2_hidden @ X8 @ X7)
% 6.31/6.49          | (r2_hidden @ X8 @ X5)
% 6.31/6.49          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 6.31/6.49      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.31/6.49  thf('28', plain,
% 6.31/6.49      (![X5 : $i, X7 : $i, X8 : $i]:
% 6.31/6.49         ((r2_hidden @ X8 @ X5)
% 6.31/6.49          | (r2_hidden @ X8 @ X7)
% 6.31/6.49          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 6.31/6.49      inference('simplify', [status(thm)], ['27'])).
% 6.31/6.49  thf('29', plain,
% 6.31/6.49      (![X0 : $i, X1 : $i]:
% 6.31/6.49         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 6.31/6.49          | (r2_hidden @ X1 @ X0)
% 6.31/6.49          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 6.31/6.49      inference('sup-', [status(thm)], ['26', '28'])).
% 6.31/6.49  thf('30', plain,
% 6.31/6.49      (![X0 : $i, X1 : $i]:
% 6.31/6.49         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 6.31/6.49          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 6.31/6.49          | ~ (v3_ordinal1 @ X1)
% 6.31/6.49          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.31/6.49          | (r2_hidden @ X1 @ X0))),
% 6.31/6.49      inference('sup-', [status(thm)], ['25', '29'])).
% 6.31/6.49  thf('31', plain,
% 6.31/6.49      (![X0 : $i, X1 : $i]:
% 6.31/6.49         (~ (v3_ordinal1 @ X0)
% 6.31/6.49          | (r2_hidden @ X1 @ X0)
% 6.31/6.49          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.31/6.49          | ~ (v3_ordinal1 @ X1)
% 6.31/6.49          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 6.31/6.49      inference('sup-', [status(thm)], ['24', '30'])).
% 6.31/6.49  thf(d1_tarski, axiom,
% 6.31/6.49    (![A:$i,B:$i]:
% 6.31/6.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 6.31/6.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 6.31/6.49  thf('32', plain,
% 6.31/6.49      (![X13 : $i, X15 : $i, X16 : $i]:
% 6.31/6.49         (~ (r2_hidden @ X16 @ X15)
% 6.31/6.49          | ((X16) = (X13))
% 6.31/6.49          | ((X15) != (k1_tarski @ X13)))),
% 6.31/6.49      inference('cnf', [status(esa)], [d1_tarski])).
% 6.31/6.49  thf('33', plain,
% 6.31/6.49      (![X13 : $i, X16 : $i]:
% 6.31/6.49         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 6.31/6.49      inference('simplify', [status(thm)], ['32'])).
% 6.31/6.49  thf('34', plain,
% 6.31/6.49      (![X0 : $i, X1 : $i]:
% 6.31/6.49         ((r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 6.31/6.49          | ~ (v3_ordinal1 @ X1)
% 6.31/6.49          | (r2_hidden @ X1 @ X0)
% 6.31/6.49          | ~ (v3_ordinal1 @ X0)
% 6.31/6.49          | ((X1) = (X0)))),
% 6.31/6.49      inference('sup-', [status(thm)], ['31', '33'])).
% 6.31/6.49  thf('35', plain,
% 6.31/6.49      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 6.31/6.49         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 6.31/6.49      inference('split', [status(esa)], ['4'])).
% 6.31/6.49  thf('36', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 6.31/6.49      inference('sat_resolution*', [status(thm)], ['5', '20'])).
% 6.31/6.49  thf('37', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 6.31/6.49      inference('simpl_trail', [status(thm)], ['35', '36'])).
% 6.31/6.49  thf('38', plain,
% 6.31/6.49      ((((sk_B) = (sk_A))
% 6.31/6.49        | ~ (v3_ordinal1 @ sk_A)
% 6.31/6.49        | (r2_hidden @ sk_B @ sk_A)
% 6.31/6.49        | ~ (v3_ordinal1 @ sk_B))),
% 6.31/6.49      inference('sup-', [status(thm)], ['34', '37'])).
% 6.31/6.49  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('41', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 6.31/6.49      inference('demod', [status(thm)], ['38', '39', '40'])).
% 6.31/6.49  thf('42', plain,
% 6.31/6.49      (![X27 : $i, X28 : $i]:
% 6.31/6.49         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 6.31/6.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 6.31/6.49  thf('43', plain, ((((sk_B) = (sk_A)) | ~ (r1_tarski @ sk_A @ sk_B))),
% 6.31/6.49      inference('sup-', [status(thm)], ['41', '42'])).
% 6.31/6.49  thf(connectedness_r1_ordinal1, axiom,
% 6.31/6.49    (![A:$i,B:$i]:
% 6.31/6.49     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 6.31/6.49       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 6.31/6.49  thf('44', plain,
% 6.31/6.49      (![X18 : $i, X19 : $i]:
% 6.31/6.49         (~ (v3_ordinal1 @ X18)
% 6.31/6.49          | ~ (v3_ordinal1 @ X19)
% 6.31/6.49          | (r1_ordinal1 @ X18 @ X19)
% 6.31/6.49          | (r1_ordinal1 @ X19 @ X18))),
% 6.31/6.49      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 6.31/6.49  thf('45', plain,
% 6.31/6.49      (![X21 : $i, X22 : $i]:
% 6.31/6.49         (~ (v3_ordinal1 @ X21)
% 6.31/6.49          | ~ (v3_ordinal1 @ X22)
% 6.31/6.49          | (r1_tarski @ X21 @ X22)
% 6.31/6.49          | ~ (r1_ordinal1 @ X21 @ X22))),
% 6.31/6.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 6.31/6.49  thf('46', plain,
% 6.31/6.49      (![X0 : $i, X1 : $i]:
% 6.31/6.49         ((r1_ordinal1 @ X0 @ X1)
% 6.31/6.49          | ~ (v3_ordinal1 @ X0)
% 6.31/6.49          | ~ (v3_ordinal1 @ X1)
% 6.31/6.49          | (r1_tarski @ X1 @ X0)
% 6.31/6.49          | ~ (v3_ordinal1 @ X0)
% 6.31/6.49          | ~ (v3_ordinal1 @ X1))),
% 6.31/6.49      inference('sup-', [status(thm)], ['44', '45'])).
% 6.31/6.49  thf('47', plain,
% 6.31/6.49      (![X0 : $i, X1 : $i]:
% 6.31/6.49         ((r1_tarski @ X1 @ X0)
% 6.31/6.49          | ~ (v3_ordinal1 @ X1)
% 6.31/6.49          | ~ (v3_ordinal1 @ X0)
% 6.31/6.49          | (r1_ordinal1 @ X0 @ X1))),
% 6.31/6.49      inference('simplify', [status(thm)], ['46'])).
% 6.31/6.49  thf('48', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 6.31/6.49      inference('simpl_trail', [status(thm)], ['3', '22'])).
% 6.31/6.49  thf('49', plain,
% 6.31/6.49      (((r1_ordinal1 @ sk_A @ sk_B)
% 6.31/6.49        | ~ (v3_ordinal1 @ sk_A)
% 6.31/6.49        | ~ (v3_ordinal1 @ sk_B))),
% 6.31/6.49      inference('sup-', [status(thm)], ['47', '48'])).
% 6.31/6.49  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('51', plain, ((v3_ordinal1 @ sk_B)),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('52', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 6.31/6.49      inference('demod', [status(thm)], ['49', '50', '51'])).
% 6.31/6.49  thf('53', plain,
% 6.31/6.49      (![X21 : $i, X22 : $i]:
% 6.31/6.49         (~ (v3_ordinal1 @ X21)
% 6.31/6.49          | ~ (v3_ordinal1 @ X22)
% 6.31/6.49          | (r1_tarski @ X21 @ X22)
% 6.31/6.49          | ~ (r1_ordinal1 @ X21 @ X22))),
% 6.31/6.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 6.31/6.49  thf('54', plain,
% 6.31/6.49      (((r1_tarski @ sk_A @ sk_B)
% 6.31/6.49        | ~ (v3_ordinal1 @ sk_B)
% 6.31/6.49        | ~ (v3_ordinal1 @ sk_A))),
% 6.31/6.49      inference('sup-', [status(thm)], ['52', '53'])).
% 6.31/6.49  thf('55', plain, ((v3_ordinal1 @ sk_B)),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('56', plain, ((v3_ordinal1 @ sk_A)),
% 6.31/6.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.49  thf('57', plain, ((r1_tarski @ sk_A @ sk_B)),
% 6.31/6.49      inference('demod', [status(thm)], ['54', '55', '56'])).
% 6.31/6.49  thf('58', plain, (((sk_B) = (sk_A))),
% 6.31/6.49      inference('demod', [status(thm)], ['43', '57'])).
% 6.31/6.49  thf(d10_xboole_0, axiom,
% 6.31/6.49    (![A:$i,B:$i]:
% 6.31/6.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.31/6.49  thf('59', plain,
% 6.31/6.49      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 6.31/6.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.31/6.49  thf('60', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 6.31/6.49      inference('simplify', [status(thm)], ['59'])).
% 6.31/6.49  thf('61', plain, ($false),
% 6.31/6.49      inference('demod', [status(thm)], ['23', '58', '60'])).
% 6.31/6.49  
% 6.31/6.49  % SZS output end Refutation
% 6.31/6.49  
% 6.31/6.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
