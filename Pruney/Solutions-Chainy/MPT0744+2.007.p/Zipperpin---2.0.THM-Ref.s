%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WdvRywTFQe

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:00 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 174 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  524 (1326 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('14',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( r2_hidden @ X21 @ X20 )
      | ~ ( r2_xboole_0 @ X21 @ X20 )
      | ~ ( v1_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('16',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( v1_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('19',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      | ( sk_A = sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['5','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('30',plain,(
    ! [X19: $i] :
      ( r2_hidden @ X19 @ ( k1_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( r1_ordinal1 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('36',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('42',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('43',plain,(
    ! [X14: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('44',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('46',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('50',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','31','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('52',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['33','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WdvRywTFQe
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 191 iterations in 0.096s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.35/0.54  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.35/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.35/0.54  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.35/0.54  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.35/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.54  thf(t34_ordinal1, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.35/0.54           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.35/0.54             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( v3_ordinal1 @ A ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( v3_ordinal1 @ B ) =>
% 0.35/0.54              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.35/0.54                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.35/0.54        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.35/0.54       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf(t69_enumset1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.54  thf('3', plain, (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.54  thf(d1_ordinal1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X16 : $i]:
% 0.35/0.54         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('split', [status(esa)], ['6'])).
% 0.35/0.54  thf(redefinition_r1_ordinal1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.35/0.54       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X17 : $i, X18 : $i]:
% 0.35/0.54         (~ (v3_ordinal1 @ X17)
% 0.35/0.54          | ~ (v3_ordinal1 @ X18)
% 0.35/0.54          | (r1_tarski @ X17 @ X18)
% 0.35/0.54          | ~ (r1_ordinal1 @ X17 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      ((((r1_tarski @ sk_A @ sk_B)
% 0.35/0.54         | ~ (v3_ordinal1 @ sk_B)
% 0.35/0.54         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.54  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.35/0.54  thf(d8_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.35/0.54       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X8 : $i, X10 : $i]:
% 0.35/0.54         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.35/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B)))
% 0.35/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf(t21_ordinal1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_ordinal1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.35/0.54           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X20 : $i, X21 : $i]:
% 0.35/0.54         (~ (v3_ordinal1 @ X20)
% 0.35/0.54          | (r2_hidden @ X21 @ X20)
% 0.35/0.54          | ~ (r2_xboole_0 @ X21 @ X20)
% 0.35/0.54          | ~ (v1_ordinal1 @ X21))),
% 0.35/0.54      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (((((sk_A) = (sk_B))
% 0.35/0.54         | ~ (v1_ordinal1 @ sk_A)
% 0.35/0.54         | (r2_hidden @ sk_A @ sk_B)
% 0.35/0.54         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.54  thf('17', plain, ((v3_ordinal1 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc1_ordinal1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X15 : $i]: ((v1_ordinal1 @ X15) | ~ (v3_ordinal1 @ X15))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.35/0.54  thf('19', plain, ((v1_ordinal1 @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf('20', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.35/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.35/0.54  thf(d3_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.35/0.54       ( ![D:$i]:
% 0.35/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.54           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X2 @ X5)
% 0.35/0.54          | (r2_hidden @ X2 @ X4)
% 0.35/0.54          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.35/0.54         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.35/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      ((![X0 : $i]:
% 0.35/0.54          (((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.35/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['21', '23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)) | ((sk_A) = (sk_B))))
% 0.35/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['5', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.35/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      ((((sk_A) = (sk_B)))
% 0.35/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.35/0.54             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.35/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.35/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.35/0.54             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.54  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.35/0.54  thf('30', plain, (![X19 : $i]: (r2_hidden @ X19 @ (k1_ordinal1 @ X19))),
% 0.35/0.54      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.35/0.54       ~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.35/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('32', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.35/0.54  thf('33', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.35/0.54  thf(t26_ordinal1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.35/0.54           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (![X22 : $i, X23 : $i]:
% 0.35/0.54         (~ (v3_ordinal1 @ X22)
% 0.35/0.54          | (r1_ordinal1 @ X23 @ X22)
% 0.35/0.54          | (r2_hidden @ X22 @ X23)
% 0.35/0.54          | ~ (v3_ordinal1 @ X23))),
% 0.35/0.54      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.35/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.54      inference('split', [status(esa)], ['6'])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X16 : $i]:
% 0.35/0.54         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X6 @ X4)
% 0.35/0.54          | (r2_hidden @ X6 @ X5)
% 0.35/0.54          | (r2_hidden @ X6 @ X3)
% 0.35/0.54          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         ((r2_hidden @ X6 @ X3)
% 0.35/0.54          | (r2_hidden @ X6 @ X5)
% 0.35/0.54          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.35/0.54          | (r2_hidden @ X1 @ X0)
% 0.35/0.54          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['36', '38'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.35/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['35', '39'])).
% 0.35/0.54  thf(l49_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i]:
% 0.35/0.54         ((r1_tarski @ X12 @ (k3_tarski @ X13)) | ~ (r2_hidden @ X12 @ X13))),
% 0.35/0.54      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      ((((r2_hidden @ sk_A @ sk_B)
% 0.35/0.54         | (r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B)))))
% 0.35/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.54  thf(t31_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.35/0.54  thf('43', plain, (![X14 : $i]: ((k3_tarski @ (k1_tarski @ X14)) = (X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      ((((r2_hidden @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B)))
% 0.35/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.35/0.54  thf(antisymmetry_r2_hidden, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.54      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      ((((r1_tarski @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.35/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.35/0.54  thf(t7_ordinal1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      (![X24 : $i, X25 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.35/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.54      inference('clc', [status(thm)], ['46', '47'])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.35/0.54       ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.35/0.54      inference('split', [status(esa)], ['6'])).
% 0.35/0.54  thf('50', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['2', '31', '49'])).
% 0.35/0.54  thf('51', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      ((~ (v3_ordinal1 @ sk_A)
% 0.35/0.54        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.35/0.54        | ~ (v3_ordinal1 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['34', '51'])).
% 0.35/0.54  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('54', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('55', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.35/0.54      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.35/0.54  thf('56', plain, ($false), inference('demod', [status(thm)], ['33', '55'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
