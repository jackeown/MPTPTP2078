%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ug3FAuQguN

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:06 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 121 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  484 ( 984 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('2',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( v3_ordinal1 @ X65 )
      | ~ ( v3_ordinal1 @ X66 )
      | ( r1_ordinal1 @ X65 @ X66 )
      | ( r1_ordinal1 @ X66 @ X65 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ~ ( v3_ordinal1 @ X69 )
      | ( r1_tarski @ X68 @ X69 )
      | ~ ( r1_ordinal1 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('12',plain,(
    ! [X70: $i,X71: $i] :
      ( ( X71 = X70 )
      | ( r2_hidden @ X71 @ X70 )
      | ~ ( r2_hidden @ X71 @ ( k1_ordinal1 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X77: $i,X78: $i] :
      ( ~ ( r2_hidden @ X77 @ X78 )
      | ~ ( r1_tarski @ X78 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('15',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('24',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','26'])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('29',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( v3_ordinal1 @ X75 )
      | ( r1_ordinal1 @ X76 @ X75 )
      | ( r2_hidden @ X75 @ X76 )
      | ~ ( v3_ordinal1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('30',plain,(
    ! [X71: $i,X72: $i] :
      ( ( r2_hidden @ X71 @ ( k1_ordinal1 @ X72 ) )
      | ~ ( r2_hidden @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ~ ( v3_ordinal1 @ X69 )
      | ( r1_tarski @ X68 @ X69 )
      | ~ ( r1_ordinal1 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('38',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('43',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ~ ( v3_ordinal1 @ X69 )
      | ( r1_tarski @ X68 @ X69 )
      | ~ ( r1_ordinal1 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('44',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X71: $i,X72: $i] :
      ( ( r2_hidden @ X71 @ ( k1_ordinal1 @ X72 ) )
      | ( X71 != X72 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('54',plain,(
    ! [X72: $i] :
      ( r2_hidden @ X72 @ ( k1_ordinal1 @ X72 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ug3FAuQguN
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:22:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 592 iterations in 0.259s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.71  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.50/0.71  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.50/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.71  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(t34_ordinal1, conjecture,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( v3_ordinal1 @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( v3_ordinal1 @ B ) =>
% 0.50/0.71           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.50/0.71             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i]:
% 0.50/0.71        ( ( v3_ordinal1 @ A ) =>
% 0.50/0.71          ( ![B:$i]:
% 0.50/0.71            ( ( v3_ordinal1 @ B ) =>
% 0.50/0.71              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.50/0.71                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.50/0.71        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.71       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('2', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(connectedness_r1_ordinal1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.50/0.71       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      (![X65 : $i, X66 : $i]:
% 0.50/0.71         (~ (v3_ordinal1 @ X65)
% 0.50/0.71          | ~ (v3_ordinal1 @ X66)
% 0.50/0.71          | (r1_ordinal1 @ X65 @ X66)
% 0.50/0.71          | (r1_ordinal1 @ X66 @ X65))),
% 0.50/0.71      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_ordinal1 @ X0 @ sk_A)
% 0.50/0.71          | (r1_ordinal1 @ sk_A @ X0)
% 0.50/0.71          | ~ (v3_ordinal1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf(redefinition_r1_ordinal1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.50/0.71       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X68 : $i, X69 : $i]:
% 0.50/0.71         (~ (v3_ordinal1 @ X68)
% 0.50/0.71          | ~ (v3_ordinal1 @ X69)
% 0.50/0.71          | (r1_tarski @ X68 @ X69)
% 0.50/0.71          | ~ (r1_ordinal1 @ X68 @ X69))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (v3_ordinal1 @ X0)
% 0.50/0.71          | (r1_ordinal1 @ sk_A @ X0)
% 0.50/0.71          | (r1_tarski @ X0 @ sk_A)
% 0.50/0.71          | ~ (v3_ordinal1 @ sk_A)
% 0.50/0.71          | ~ (v3_ordinal1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.71  thf('7', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (v3_ordinal1 @ X0)
% 0.50/0.71          | (r1_ordinal1 @ sk_A @ X0)
% 0.50/0.71          | (r1_tarski @ X0 @ sk_A)
% 0.50/0.71          | ~ (v3_ordinal1 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_tarski @ X0 @ sk_A)
% 0.50/0.71          | (r1_ordinal1 @ sk_A @ X0)
% 0.50/0.71          | ~ (v3_ordinal1 @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['8'])).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('11', plain,
% 0.50/0.71      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.71         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('split', [status(esa)], ['10'])).
% 0.50/0.71  thf(t13_ordinal1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.50/0.71       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      (![X70 : $i, X71 : $i]:
% 0.50/0.71         (((X71) = (X70))
% 0.50/0.71          | (r2_hidden @ X71 @ X70)
% 0.50/0.71          | ~ (r2_hidden @ X71 @ (k1_ordinal1 @ X70)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.50/0.71         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.71  thf(t7_ordinal1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X77 : $i, X78 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X77 @ X78) | ~ (r1_tarski @ X78 @ X77))),
% 0.50/0.71      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.50/0.71  thf('15', plain,
% 0.50/0.71      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.50/0.71         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      (((~ (v3_ordinal1 @ sk_B)
% 0.50/0.71         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.50/0.71         | ((sk_A) = (sk_B)))) <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['9', '15'])).
% 0.50/0.71  thf('17', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      ((((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.50/0.71         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('20', plain,
% 0.50/0.71      ((((sk_A) = (sk_B)))
% 0.50/0.71         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.50/0.71             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.50/0.71         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.50/0.71             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_ordinal1 @ X0 @ sk_A)
% 0.50/0.71          | (r1_ordinal1 @ sk_A @ X0)
% 0.50/0.71          | ~ (v3_ordinal1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf('24', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.50/0.71      inference('eq_fact', [status(thm)], ['23'])).
% 0.50/0.71  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('26', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.50/0.71      inference('demod', [status(thm)], ['24', '25'])).
% 0.50/0.71  thf('27', plain,
% 0.50/0.71      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.71       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['22', '26'])).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.71       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.71      inference('split', [status(esa)], ['10'])).
% 0.50/0.71  thf(t26_ordinal1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( v3_ordinal1 @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( v3_ordinal1 @ B ) =>
% 0.50/0.71           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      (![X75 : $i, X76 : $i]:
% 0.50/0.71         (~ (v3_ordinal1 @ X75)
% 0.50/0.71          | (r1_ordinal1 @ X76 @ X75)
% 0.50/0.71          | (r2_hidden @ X75 @ X76)
% 0.50/0.71          | ~ (v3_ordinal1 @ X76))),
% 0.50/0.71      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.50/0.71  thf('30', plain,
% 0.50/0.71      (![X71 : $i, X72 : $i]:
% 0.50/0.71         ((r2_hidden @ X71 @ (k1_ordinal1 @ X72)) | ~ (r2_hidden @ X71 @ X72))),
% 0.50/0.71      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (v3_ordinal1 @ X0)
% 0.50/0.71          | (r1_ordinal1 @ X0 @ X1)
% 0.50/0.71          | ~ (v3_ordinal1 @ X1)
% 0.50/0.71          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.71  thf('32', plain,
% 0.50/0.71      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.71         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (((~ (v3_ordinal1 @ sk_A)
% 0.50/0.71         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.50/0.71         | ~ (v3_ordinal1 @ sk_B)))
% 0.50/0.71         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.71  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('36', plain,
% 0.50/0.71      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.50/0.71         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.50/0.71  thf('37', plain,
% 0.50/0.71      (![X68 : $i, X69 : $i]:
% 0.50/0.71         (~ (v3_ordinal1 @ X68)
% 0.50/0.71          | ~ (v3_ordinal1 @ X69)
% 0.50/0.71          | (r1_tarski @ X68 @ X69)
% 0.50/0.71          | ~ (r1_ordinal1 @ X68 @ X69))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.50/0.71  thf('38', plain,
% 0.50/0.71      ((((r1_tarski @ sk_B @ sk_A)
% 0.50/0.71         | ~ (v3_ordinal1 @ sk_A)
% 0.50/0.71         | ~ (v3_ordinal1 @ sk_B)))
% 0.50/0.71         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.71  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('41', plain,
% 0.50/0.71      (((r1_tarski @ sk_B @ sk_A))
% 0.50/0.71         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.50/0.71  thf('42', plain,
% 0.50/0.71      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('split', [status(esa)], ['10'])).
% 0.50/0.71  thf('43', plain,
% 0.50/0.71      (![X68 : $i, X69 : $i]:
% 0.50/0.71         (~ (v3_ordinal1 @ X68)
% 0.50/0.71          | ~ (v3_ordinal1 @ X69)
% 0.50/0.71          | (r1_tarski @ X68 @ X69)
% 0.50/0.71          | ~ (r1_ordinal1 @ X68 @ X69))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      ((((r1_tarski @ sk_A @ sk_B)
% 0.50/0.71         | ~ (v3_ordinal1 @ sk_B)
% 0.50/0.71         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.71  thf('45', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('47', plain,
% 0.50/0.71      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.50/0.71  thf(d10_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.71  thf('48', plain,
% 0.50/0.71      (![X10 : $i, X12 : $i]:
% 0.50/0.71         (((X10) = (X12))
% 0.50/0.71          | ~ (r1_tarski @ X12 @ X10)
% 0.50/0.71          | ~ (r1_tarski @ X10 @ X12))),
% 0.50/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.71  thf('49', plain,
% 0.50/0.71      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 0.50/0.71         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.71  thf('50', plain,
% 0.50/0.71      ((((sk_B) = (sk_A)))
% 0.50/0.71         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.50/0.71             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['41', '49'])).
% 0.50/0.71  thf('51', plain,
% 0.50/0.71      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.71         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('52', plain,
% 0.50/0.71      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.50/0.71         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.50/0.71             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.50/0.71  thf('53', plain,
% 0.50/0.71      (![X71 : $i, X72 : $i]:
% 0.50/0.71         ((r2_hidden @ X71 @ (k1_ordinal1 @ X72)) | ((X71) != (X72)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.50/0.71  thf('54', plain, (![X72 : $i]: (r2_hidden @ X72 @ (k1_ordinal1 @ X72))),
% 0.50/0.71      inference('simplify', [status(thm)], ['53'])).
% 0.50/0.71  thf('55', plain,
% 0.50/0.71      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.71       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['52', '54'])).
% 0.50/0.71  thf('56', plain, ($false),
% 0.50/0.71      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '55'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
