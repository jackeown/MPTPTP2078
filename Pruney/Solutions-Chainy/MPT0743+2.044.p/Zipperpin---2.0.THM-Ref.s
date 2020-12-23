%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EDk7k6F20I

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:58 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 234 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   24
%              Number of atoms          :  490 (1815 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X35 ) )
      | ~ ( v3_ordinal1 @ X35 ) ) ),
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

thf('3',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('5',plain,(
    ! [X34: $i] :
      ( r2_hidden @ X34 @ ( k1_ordinal1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('6',plain,(
    ! [X35: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X35 ) )
      | ~ ( v3_ordinal1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('7',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_ordinal1 @ X32 )
      | ~ ( v3_ordinal1 @ X33 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_ordinal1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('21',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['4','19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['2','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['2','21'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X25 @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r2_hidden @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v3_ordinal1 @ X29 )
      | ~ ( v3_ordinal1 @ X30 )
      | ( r1_ordinal1 @ X29 @ X30 )
      | ( r1_ordinal1 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_ordinal1 @ X32 )
      | ~ ( v3_ordinal1 @ X33 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_ordinal1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r1_tarski @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['4','19','20'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_ordinal1 @ X32 )
      | ~ ( v3_ordinal1 @ X33 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_ordinal1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('43',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_B ),
    inference('sup-',[status(thm)],['28','48'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('50',plain,(
    ! [X31: $i] :
      ( ( k1_ordinal1 @ X31 )
      = ( k2_xboole_0 @ X31 @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('51',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_ordinal1 @ X32 )
      | ~ ( v3_ordinal1 @ X33 )
      | ( r1_ordinal1 @ X32 @ X33 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('53',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('57',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','19'])).

thf('58',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','58'])).

thf('60',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EDk7k6F20I
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.77  % Solved by: fo/fo7.sh
% 0.57/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.77  % done 822 iterations in 0.314s
% 0.57/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.77  % SZS output start Refutation
% 0.57/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.57/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.77  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.57/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.77  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.57/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.77  thf(t29_ordinal1, axiom,
% 0.57/0.77    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.57/0.77  thf('0', plain,
% 0.57/0.77      (![X35 : $i]:
% 0.57/0.77         ((v3_ordinal1 @ (k1_ordinal1 @ X35)) | ~ (v3_ordinal1 @ X35))),
% 0.57/0.77      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.57/0.77  thf(t33_ordinal1, conjecture,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( v3_ordinal1 @ A ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( v3_ordinal1 @ B ) =>
% 0.57/0.77           ( ( r2_hidden @ A @ B ) <=>
% 0.57/0.77             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.57/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.77    (~( ![A:$i]:
% 0.57/0.77        ( ( v3_ordinal1 @ A ) =>
% 0.57/0.77          ( ![B:$i]:
% 0.57/0.77            ( ( v3_ordinal1 @ B ) =>
% 0.57/0.77              ( ( r2_hidden @ A @ B ) <=>
% 0.57/0.77                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.57/0.77    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.57/0.77  thf('1', plain,
% 0.57/0.77      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('2', plain,
% 0.57/0.77      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.57/0.77      inference('split', [status(esa)], ['1'])).
% 0.57/0.77  thf('3', plain,
% 0.57/0.77      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.57/0.77        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('4', plain,
% 0.57/0.77      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.57/0.77       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.57/0.77      inference('split', [status(esa)], ['3'])).
% 0.57/0.77  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.57/0.77  thf('5', plain, (![X34 : $i]: (r2_hidden @ X34 @ (k1_ordinal1 @ X34))),
% 0.57/0.77      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.57/0.77  thf('6', plain,
% 0.57/0.77      (![X35 : $i]:
% 0.57/0.77         ((v3_ordinal1 @ (k1_ordinal1 @ X35)) | ~ (v3_ordinal1 @ X35))),
% 0.57/0.77      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.57/0.77  thf('7', plain,
% 0.57/0.77      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.57/0.77         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.57/0.77      inference('split', [status(esa)], ['1'])).
% 0.57/0.77  thf(redefinition_r1_ordinal1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.57/0.77       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.57/0.77  thf('8', plain,
% 0.57/0.77      (![X32 : $i, X33 : $i]:
% 0.57/0.77         (~ (v3_ordinal1 @ X32)
% 0.57/0.77          | ~ (v3_ordinal1 @ X33)
% 0.57/0.77          | (r1_tarski @ X32 @ X33)
% 0.57/0.77          | ~ (r1_ordinal1 @ X32 @ X33))),
% 0.57/0.77      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.57/0.77  thf('9', plain,
% 0.57/0.77      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.57/0.77         | ~ (v3_ordinal1 @ sk_B)
% 0.57/0.77         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.57/0.77         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.77  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('11', plain,
% 0.57/0.77      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.57/0.77         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.57/0.77         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.57/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.77  thf('12', plain,
% 0.57/0.77      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.57/0.77         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['6', '11'])).
% 0.57/0.77  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('14', plain,
% 0.57/0.77      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.57/0.77         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.57/0.77      inference('demod', [status(thm)], ['12', '13'])).
% 0.57/0.77  thf(d3_tarski, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.77  thf('15', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.57/0.77          | (r2_hidden @ X0 @ X2)
% 0.57/0.77          | ~ (r1_tarski @ X1 @ X2))),
% 0.57/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.77  thf('16', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 0.57/0.77         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.57/0.77  thf('17', plain,
% 0.57/0.77      (((r2_hidden @ sk_A @ sk_B))
% 0.57/0.77         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['5', '16'])).
% 0.57/0.77  thf('18', plain,
% 0.57/0.77      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.57/0.77      inference('split', [status(esa)], ['3'])).
% 0.57/0.77  thf('19', plain,
% 0.57/0.77      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.57/0.77       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.57/0.77  thf('20', plain,
% 0.57/0.77      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.57/0.77       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.57/0.77      inference('split', [status(esa)], ['1'])).
% 0.57/0.77  thf('21', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.57/0.77      inference('sat_resolution*', [status(thm)], ['4', '19', '20'])).
% 0.57/0.77  thf('22', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.57/0.77      inference('simpl_trail', [status(thm)], ['2', '21'])).
% 0.57/0.77  thf('23', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.57/0.77      inference('simpl_trail', [status(thm)], ['2', '21'])).
% 0.57/0.77  thf(t38_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.57/0.77       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.57/0.77  thf('24', plain,
% 0.57/0.77      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.57/0.77         ((r1_tarski @ (k2_tarski @ X25 @ X27) @ X28)
% 0.57/0.77          | ~ (r2_hidden @ X27 @ X28)
% 0.57/0.77          | ~ (r2_hidden @ X25 @ X28))),
% 0.57/0.77      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.57/0.77  thf('25', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (~ (r2_hidden @ X0 @ sk_B)
% 0.57/0.77          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.57/0.77  thf('26', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.57/0.77      inference('sup-', [status(thm)], ['22', '25'])).
% 0.57/0.77  thf(t69_enumset1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.77  thf('27', plain,
% 0.57/0.77      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.57/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.77  thf('28', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.57/0.77      inference('demod', [status(thm)], ['26', '27'])).
% 0.57/0.77  thf(connectedness_r1_ordinal1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.57/0.77       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.57/0.77  thf('29', plain,
% 0.57/0.77      (![X29 : $i, X30 : $i]:
% 0.57/0.77         (~ (v3_ordinal1 @ X29)
% 0.57/0.77          | ~ (v3_ordinal1 @ X30)
% 0.57/0.77          | (r1_ordinal1 @ X29 @ X30)
% 0.57/0.77          | (r1_ordinal1 @ X30 @ X29))),
% 0.57/0.77      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.57/0.77  thf('30', plain,
% 0.57/0.77      (![X32 : $i, X33 : $i]:
% 0.57/0.77         (~ (v3_ordinal1 @ X32)
% 0.57/0.77          | ~ (v3_ordinal1 @ X33)
% 0.57/0.77          | (r1_tarski @ X32 @ X33)
% 0.57/0.77          | ~ (r1_ordinal1 @ X32 @ X33))),
% 0.57/0.77      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.57/0.77  thf('31', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((r1_ordinal1 @ X0 @ X1)
% 0.57/0.77          | ~ (v3_ordinal1 @ X0)
% 0.57/0.77          | ~ (v3_ordinal1 @ X1)
% 0.57/0.77          | (r1_tarski @ X1 @ X0)
% 0.57/0.77          | ~ (v3_ordinal1 @ X0)
% 0.57/0.77          | ~ (v3_ordinal1 @ X1))),
% 0.57/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.77  thf('32', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((r1_tarski @ X1 @ X0)
% 0.57/0.77          | ~ (v3_ordinal1 @ X1)
% 0.57/0.77          | ~ (v3_ordinal1 @ X0)
% 0.57/0.77          | (r1_ordinal1 @ X0 @ X1))),
% 0.57/0.77      inference('simplify', [status(thm)], ['31'])).
% 0.57/0.77  thf('33', plain,
% 0.57/0.77      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.57/0.77      inference('split', [status(esa)], ['1'])).
% 0.57/0.77  thf(t7_ordinal1, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.77  thf('34', plain,
% 0.57/0.77      (![X36 : $i, X37 : $i]:
% 0.57/0.77         (~ (r2_hidden @ X36 @ X37) | ~ (r1_tarski @ X37 @ X36))),
% 0.57/0.77      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.57/0.77  thf('35', plain,
% 0.57/0.77      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['33', '34'])).
% 0.57/0.77  thf('36', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.57/0.77      inference('sat_resolution*', [status(thm)], ['4', '19', '20'])).
% 0.57/0.77  thf('37', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.57/0.77      inference('simpl_trail', [status(thm)], ['35', '36'])).
% 0.57/0.77  thf('38', plain,
% 0.57/0.77      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.57/0.77        | ~ (v3_ordinal1 @ sk_A)
% 0.57/0.77        | ~ (v3_ordinal1 @ sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['32', '37'])).
% 0.57/0.77  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('41', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.57/0.77      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.57/0.77  thf('42', plain,
% 0.57/0.77      (![X32 : $i, X33 : $i]:
% 0.57/0.77         (~ (v3_ordinal1 @ X32)
% 0.57/0.77          | ~ (v3_ordinal1 @ X33)
% 0.57/0.77          | (r1_tarski @ X32 @ X33)
% 0.57/0.77          | ~ (r1_ordinal1 @ X32 @ X33))),
% 0.57/0.77      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.57/0.77  thf('43', plain,
% 0.57/0.77      (((r1_tarski @ sk_A @ sk_B)
% 0.57/0.77        | ~ (v3_ordinal1 @ sk_B)
% 0.57/0.77        | ~ (v3_ordinal1 @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['41', '42'])).
% 0.57/0.77  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('46', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.57/0.77      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.57/0.77  thf(t8_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.57/0.77       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.57/0.77  thf('47', plain,
% 0.57/0.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X7 @ X8)
% 0.57/0.77          | ~ (r1_tarski @ X9 @ X8)
% 0.57/0.77          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.57/0.77      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.57/0.77  thf('48', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.57/0.77          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['46', '47'])).
% 0.57/0.77  thf('49', plain,
% 0.57/0.77      ((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ sk_B)),
% 0.57/0.77      inference('sup-', [status(thm)], ['28', '48'])).
% 0.57/0.77  thf(d1_ordinal1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.57/0.77  thf('50', plain,
% 0.57/0.77      (![X31 : $i]:
% 0.57/0.77         ((k1_ordinal1 @ X31) = (k2_xboole_0 @ X31 @ (k1_tarski @ X31)))),
% 0.57/0.77      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.57/0.77  thf('51', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.57/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.57/0.77  thf('52', plain,
% 0.57/0.77      (![X32 : $i, X33 : $i]:
% 0.57/0.77         (~ (v3_ordinal1 @ X32)
% 0.57/0.77          | ~ (v3_ordinal1 @ X33)
% 0.57/0.77          | (r1_ordinal1 @ X32 @ X33)
% 0.57/0.77          | ~ (r1_tarski @ X32 @ X33))),
% 0.57/0.77      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.57/0.77  thf('53', plain,
% 0.57/0.77      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.57/0.77        | ~ (v3_ordinal1 @ sk_B)
% 0.57/0.77        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['51', '52'])).
% 0.57/0.77  thf('54', plain, ((v3_ordinal1 @ sk_B)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('55', plain,
% 0.57/0.77      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.57/0.77        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.57/0.77      inference('demod', [status(thm)], ['53', '54'])).
% 0.57/0.77  thf('56', plain,
% 0.57/0.77      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.57/0.77         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.57/0.77      inference('split', [status(esa)], ['3'])).
% 0.57/0.77  thf('57', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.57/0.77      inference('sat_resolution*', [status(thm)], ['4', '19'])).
% 0.57/0.77  thf('58', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.57/0.77      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.57/0.77  thf('59', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))),
% 0.57/0.77      inference('clc', [status(thm)], ['55', '58'])).
% 0.57/0.77  thf('60', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.57/0.77      inference('sup-', [status(thm)], ['0', '59'])).
% 0.57/0.77  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('62', plain, ($false), inference('demod', [status(thm)], ['60', '61'])).
% 0.57/0.77  
% 0.57/0.77  % SZS output end Refutation
% 0.57/0.77  
% 0.57/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
