%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SiYS77ce3y

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X34: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
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
    ! [X33: $i] :
      ( r2_hidden @ X33 @ ( k1_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('6',plain,(
    ! [X34: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( v3_ordinal1 @ X32 )
      | ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_ordinal1 @ X31 @ X32 ) ) ),
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
    ! [X24: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X24 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ X24 @ X27 ) ) ),
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
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( v3_ordinal1 @ X28 )
      | ~ ( v3_ordinal1 @ X29 )
      | ( r1_ordinal1 @ X28 @ X29 )
      | ( r1_ordinal1 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('30',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( v3_ordinal1 @ X32 )
      | ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_ordinal1 @ X31 @ X32 ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( v3_ordinal1 @ X32 )
      | ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_ordinal1 @ X31 @ X32 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
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
    ! [X30: $i] :
      ( ( k1_ordinal1 @ X30 )
      = ( k2_xboole_0 @ X30 @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('51',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( v3_ordinal1 @ X32 )
      | ( r1_ordinal1 @ X31 @ X32 )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SiYS77ce3y
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 289 iterations in 0.104s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.54  thf(t29_ordinal1, axiom,
% 0.20/0.54    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X34 : $i]:
% 0.20/0.54         ((v3_ordinal1 @ (k1_ordinal1 @ X34)) | ~ (v3_ordinal1 @ X34))),
% 0.20/0.54      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.54  thf(t33_ordinal1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.54           ( ( r2_hidden @ A @ B ) <=>
% 0.20/0.54             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.54              ( ( r2_hidden @ A @ B ) <=>
% 0.20/0.54                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['1'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.54        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.20/0.54       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.54  thf('5', plain, (![X33 : $i]: (r2_hidden @ X33 @ (k1_ordinal1 @ X33))),
% 0.20/0.54      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X34 : $i]:
% 0.20/0.54         ((v3_ordinal1 @ (k1_ordinal1 @ X34)) | ~ (v3_ordinal1 @ X34))),
% 0.20/0.54      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.54         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['1'])).
% 0.20/0.54  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.54       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i]:
% 0.20/0.54         (~ (v3_ordinal1 @ X31)
% 0.20/0.54          | ~ (v3_ordinal1 @ X32)
% 0.20/0.54          | (r1_tarski @ X31 @ X32)
% 0.20/0.54          | ~ (r1_ordinal1 @ X31 @ X32))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.54         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.54         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.54         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.54         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.54         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.20/0.54         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.54  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.54         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf(d3_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.54         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B))
% 0.20/0.54         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.54       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.54       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['1'])).
% 0.20/0.54  thf('21', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['4', '19', '20'])).
% 0.20/0.54  thf('22', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['2', '21'])).
% 0.20/0.54  thf('23', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['2', '21'])).
% 0.20/0.54  thf(t38_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.20/0.54         ((r1_tarski @ (k2_tarski @ X24 @ X26) @ X27)
% 0.20/0.54          | ~ (r2_hidden @ X26 @ X27)
% 0.20/0.54          | ~ (r2_hidden @ X24 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.54          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.54  thf(t69_enumset1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.54  thf('27', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf('28', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf(connectedness_r1_ordinal1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.54       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (v3_ordinal1 @ X28)
% 0.20/0.54          | ~ (v3_ordinal1 @ X29)
% 0.20/0.54          | (r1_ordinal1 @ X28 @ X29)
% 0.20/0.54          | (r1_ordinal1 @ X29 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i]:
% 0.20/0.54         (~ (v3_ordinal1 @ X31)
% 0.20/0.54          | ~ (v3_ordinal1 @ X32)
% 0.20/0.54          | (r1_tarski @ X31 @ X32)
% 0.20/0.54          | ~ (r1_ordinal1 @ X31 @ X32))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.54          | ~ (v3_ordinal1 @ X0)
% 0.20/0.54          | ~ (v3_ordinal1 @ X1)
% 0.20/0.54          | (r1_tarski @ X1 @ X0)
% 0.20/0.54          | ~ (v3_ordinal1 @ X0)
% 0.20/0.54          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X0)
% 0.20/0.54          | ~ (v3_ordinal1 @ X1)
% 0.20/0.54          | ~ (v3_ordinal1 @ X0)
% 0.20/0.54          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['1'])).
% 0.20/0.54  thf(t7_ordinal1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X35 : $i, X36 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('36', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['4', '19', '20'])).
% 0.20/0.54  thf('37', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.54        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.54        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['32', '37'])).
% 0.20/0.54  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('41', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i]:
% 0.20/0.54         (~ (v3_ordinal1 @ X31)
% 0.20/0.54          | ~ (v3_ordinal1 @ X32)
% 0.20/0.54          | (r1_tarski @ X31 @ X32)
% 0.20/0.54          | ~ (r1_ordinal1 @ X31 @ X32))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((r1_tarski @ sk_A @ sk_B)
% 0.20/0.54        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.54        | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('46', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.54  thf(t8_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.20/0.54       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X4 @ X5)
% 0.20/0.54          | ~ (r1_tarski @ X6 @ X5)
% 0.20/0.54          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.20/0.54          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['28', '48'])).
% 0.20/0.54  thf(d1_ordinal1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X30 : $i]:
% 0.20/0.54         ((k1_ordinal1 @ X30) = (k2_xboole_0 @ X30 @ (k1_tarski @ X30)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.54  thf('51', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i]:
% 0.20/0.54         (~ (v3_ordinal1 @ X31)
% 0.20/0.54          | ~ (v3_ordinal1 @ X32)
% 0.20/0.54          | (r1_ordinal1 @ X31 @ X32)
% 0.20/0.54          | ~ (r1_tarski @ X31 @ X32))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.54        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.54        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('54', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.54        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.54         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('57', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['4', '19'])).
% 0.20/0.54  thf('58', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.20/0.54  thf('59', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['55', '58'])).
% 0.20/0.54  thf('60', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '59'])).
% 0.20/0.54  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('62', plain, ($false), inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
