%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GzH2gKf3pJ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:58 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 191 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   24
%              Number of atoms          :  472 (1466 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

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

thf('1',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('7',plain,(
    ! [X26: $i] :
      ( r2_hidden @ X26 @ ( k1_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('8',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('9',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ~ ( v3_ordinal1 @ X25 )
      | ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_ordinal1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('11',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['6','21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['4','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ( r1_ordinal1 @ X21 @ X22 )
      | ( r1_ordinal1 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ~ ( v3_ordinal1 @ X25 )
      | ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_ordinal1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['6','21','22'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ~ ( v3_ordinal1 @ X25 )
      | ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_ordinal1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('42',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_B ),
    inference('sup-',[status(thm)],['24','47'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('49',plain,(
    ! [X23: $i] :
      ( ( k1_ordinal1 @ X23 )
      = ( k2_xboole_0 @ X23 @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('50',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ~ ( v3_ordinal1 @ X25 )
      | ( r1_ordinal1 @ X24 @ X25 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('52',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('56',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['6','21'])).

thf('57',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GzH2gKf3pJ
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 1140 iterations in 0.444s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.89  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.70/0.89  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.70/0.89  thf(t29_ordinal1, axiom,
% 0.70/0.89    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      (![X27 : $i]:
% 0.70/0.89         ((v3_ordinal1 @ (k1_ordinal1 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 0.70/0.89      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.70/0.89  thf(t33_ordinal1, conjecture,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( v3_ordinal1 @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( v3_ordinal1 @ B ) =>
% 0.70/0.89           ( ( r2_hidden @ A @ B ) <=>
% 0.70/0.89             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i]:
% 0.70/0.89        ( ( v3_ordinal1 @ A ) =>
% 0.70/0.89          ( ![B:$i]:
% 0.70/0.89            ( ( v3_ordinal1 @ B ) =>
% 0.70/0.89              ( ( r2_hidden @ A @ B ) <=>
% 0.70/0.89                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.70/0.89      inference('split', [status(esa)], ['1'])).
% 0.70/0.89  thf(l1_zfmisc_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X16 : $i, X18 : $i]:
% 0.70/0.89         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 0.70/0.89      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.70/0.89         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.70/0.89        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.70/0.89       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.70/0.89      inference('split', [status(esa)], ['5'])).
% 0.70/0.89  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.70/0.89  thf('7', plain, (![X26 : $i]: (r2_hidden @ X26 @ (k1_ordinal1 @ X26))),
% 0.70/0.89      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X27 : $i]:
% 0.70/0.89         ((v3_ordinal1 @ (k1_ordinal1 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 0.70/0.89      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.70/0.89         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.70/0.89      inference('split', [status(esa)], ['1'])).
% 0.70/0.89  thf(redefinition_r1_ordinal1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.70/0.89       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X24 : $i, X25 : $i]:
% 0.70/0.89         (~ (v3_ordinal1 @ X24)
% 0.70/0.89          | ~ (v3_ordinal1 @ X25)
% 0.70/0.89          | (r1_tarski @ X24 @ X25)
% 0.70/0.89          | ~ (r1_ordinal1 @ X24 @ X25))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.70/0.89         | ~ (v3_ordinal1 @ sk_B)
% 0.70/0.89         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.70/0.89         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.70/0.89  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.70/0.89         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.70/0.89         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.70/0.89         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['8', '13'])).
% 0.70/0.89  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.70/0.89         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['14', '15'])).
% 0.70/0.89  thf(d3_tarski, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.89          | (r2_hidden @ X0 @ X2)
% 0.70/0.89          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 0.70/0.89         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['16', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (((r2_hidden @ sk_A @ sk_B))
% 0.70/0.89         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '18'])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.70/0.89      inference('split', [status(esa)], ['5'])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.70/0.89       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['19', '20'])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.70/0.89       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.70/0.89      inference('split', [status(esa)], ['1'])).
% 0.70/0.89  thf('23', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.70/0.89      inference('sat_resolution*', [status(thm)], ['6', '21', '22'])).
% 0.70/0.89  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['4', '23'])).
% 0.70/0.89  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(connectedness_r1_ordinal1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.70/0.89       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.70/0.89  thf('26', plain,
% 0.70/0.89      (![X21 : $i, X22 : $i]:
% 0.70/0.89         (~ (v3_ordinal1 @ X21)
% 0.70/0.89          | ~ (v3_ordinal1 @ X22)
% 0.70/0.89          | (r1_ordinal1 @ X21 @ X22)
% 0.70/0.89          | (r1_ordinal1 @ X22 @ X21))),
% 0.70/0.89      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((r1_ordinal1 @ X0 @ sk_A)
% 0.70/0.89          | (r1_ordinal1 @ sk_A @ X0)
% 0.70/0.89          | ~ (v3_ordinal1 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['25', '26'])).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      (![X24 : $i, X25 : $i]:
% 0.70/0.89         (~ (v3_ordinal1 @ X24)
% 0.70/0.89          | ~ (v3_ordinal1 @ X25)
% 0.70/0.89          | (r1_tarski @ X24 @ X25)
% 0.70/0.89          | ~ (r1_ordinal1 @ X24 @ X25))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (v3_ordinal1 @ X0)
% 0.70/0.89          | (r1_ordinal1 @ sk_A @ X0)
% 0.70/0.89          | (r1_tarski @ X0 @ sk_A)
% 0.70/0.89          | ~ (v3_ordinal1 @ sk_A)
% 0.70/0.89          | ~ (v3_ordinal1 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.70/0.89  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (v3_ordinal1 @ X0)
% 0.70/0.89          | (r1_ordinal1 @ sk_A @ X0)
% 0.70/0.89          | (r1_tarski @ X0 @ sk_A)
% 0.70/0.89          | ~ (v3_ordinal1 @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((r1_tarski @ X0 @ sk_A)
% 0.70/0.89          | (r1_ordinal1 @ sk_A @ X0)
% 0.70/0.89          | ~ (v3_ordinal1 @ X0))),
% 0.70/0.89      inference('simplify', [status(thm)], ['31'])).
% 0.70/0.89  thf('33', plain,
% 0.70/0.89      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.70/0.89      inference('split', [status(esa)], ['1'])).
% 0.70/0.89  thf(t7_ordinal1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (![X28 : $i, X29 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 0.70/0.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['33', '34'])).
% 0.70/0.89  thf('36', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.70/0.89      inference('sat_resolution*', [status(thm)], ['6', '21', '22'])).
% 0.70/0.89  thf('37', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['35', '36'])).
% 0.70/0.89  thf('38', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['32', '37'])).
% 0.70/0.89  thf('39', plain, ((v3_ordinal1 @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('40', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.70/0.89      inference('demod', [status(thm)], ['38', '39'])).
% 0.70/0.89  thf('41', plain,
% 0.70/0.89      (![X24 : $i, X25 : $i]:
% 0.70/0.89         (~ (v3_ordinal1 @ X24)
% 0.70/0.89          | ~ (v3_ordinal1 @ X25)
% 0.70/0.89          | (r1_tarski @ X24 @ X25)
% 0.70/0.89          | ~ (r1_ordinal1 @ X24 @ X25))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      (((r1_tarski @ sk_A @ sk_B)
% 0.70/0.89        | ~ (v3_ordinal1 @ sk_B)
% 0.70/0.89        | ~ (v3_ordinal1 @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.70/0.89  thf('43', plain, ((v3_ordinal1 @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('44', plain, ((v3_ordinal1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('45', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.70/0.89      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.70/0.89  thf(t8_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.70/0.89       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.70/0.89  thf('46', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X7 @ X8)
% 0.70/0.89          | ~ (r1_tarski @ X9 @ X8)
% 0.70/0.89          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.70/0.89  thf('47', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.70/0.89          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['45', '46'])).
% 0.70/0.89  thf('48', plain,
% 0.70/0.89      ((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ sk_B)),
% 0.70/0.89      inference('sup-', [status(thm)], ['24', '47'])).
% 0.70/0.89  thf(d1_ordinal1, axiom,
% 0.70/0.89    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      (![X23 : $i]:
% 0.70/0.89         ((k1_ordinal1 @ X23) = (k2_xboole_0 @ X23 @ (k1_tarski @ X23)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.70/0.89  thf('50', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.70/0.89      inference('demod', [status(thm)], ['48', '49'])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      (![X24 : $i, X25 : $i]:
% 0.70/0.89         (~ (v3_ordinal1 @ X24)
% 0.70/0.89          | ~ (v3_ordinal1 @ X25)
% 0.70/0.89          | (r1_ordinal1 @ X24 @ X25)
% 0.70/0.89          | ~ (r1_tarski @ X24 @ X25))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.70/0.89  thf('52', plain,
% 0.70/0.89      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.70/0.89        | ~ (v3_ordinal1 @ sk_B)
% 0.70/0.89        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['50', '51'])).
% 0.70/0.89  thf('53', plain, ((v3_ordinal1 @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('54', plain,
% 0.70/0.89      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.70/0.89        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.70/0.89      inference('demod', [status(thm)], ['52', '53'])).
% 0.70/0.90  thf('55', plain,
% 0.70/0.90      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.70/0.90         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.70/0.90      inference('split', [status(esa)], ['5'])).
% 0.70/0.90  thf('56', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['6', '21'])).
% 0.70/0.90  thf('57', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['55', '56'])).
% 0.70/0.90  thf('58', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))),
% 0.70/0.90      inference('clc', [status(thm)], ['54', '57'])).
% 0.70/0.90  thf('59', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.70/0.90      inference('sup-', [status(thm)], ['0', '58'])).
% 0.70/0.90  thf('60', plain, ((v3_ordinal1 @ sk_A)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('61', plain, ($false), inference('demod', [status(thm)], ['59', '60'])).
% 0.70/0.90  
% 0.70/0.90  % SZS output end Refutation
% 0.70/0.90  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
