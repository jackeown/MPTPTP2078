%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4mHBROLEzX

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 104 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  365 ( 624 expanded)
%              Number of equality atoms :   41 (  66 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X13 @ X10 ) @ ( sk_D @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('9',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('19',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_relat_1 @ X1 )
         != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('34',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4mHBROLEzX
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 152 iterations in 0.088s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.54  thf(cc1_relat_1, axiom,
% 0.20/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.54  thf('0', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.54  thf(d4_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.54           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X10 : $i, X13 : $i]:
% 0.20/0.54         (((X13) = (k1_relat_1 @ X10))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (k4_tarski @ (sk_C_1 @ X13 @ X10) @ (sk_D @ X13 @ X10)) @ X10)
% 0.20/0.54          | (r2_hidden @ (sk_C_1 @ X13 @ X10) @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.54  thf(t2_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.54  thf(t4_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.20/0.54          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.54  thf('5', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.54  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.54          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.54  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('9', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf(dt_k4_relat_1, axiom,
% 0.20/0.54    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.54  thf(t37_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.20/0.54         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X17 : $i]:
% 0.20/0.54         (((k1_relat_1 @ X17) = (k2_relat_1 @ (k4_relat_1 @ X17)))
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.54  thf(fc9_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.54       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X16 : $i]:
% 0.20/0.54         (~ (v1_xboole_0 @ (k2_relat_1 @ X16))
% 0.20/0.54          | ~ (v1_relat_1 @ X16)
% 0.20/0.54          | (v1_xboole_0 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X0)
% 0.20/0.54          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.54          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X17 : $i]:
% 0.20/0.54         (((k1_relat_1 @ X17) = (k2_relat_1 @ (k4_relat_1 @ X17)))
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.54  thf(l13_xboole_0, axiom,
% 0.20/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.54  thf(t60_relat_1, conjecture,
% 0.20/0.54    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.54     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.54        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.54         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (((k2_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.20/0.54         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      ((![X0 : $i, X1 : $i]:
% 0.20/0.54          (((k2_relat_1 @ X1) != (X0))
% 0.20/0.54           | ~ (v1_xboole_0 @ X0)
% 0.20/0.54           | ~ (v1_xboole_0 @ X1)))
% 0.20/0.54         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['17', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((![X1 : $i]:
% 0.20/0.54          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_relat_1 @ X1))))
% 0.20/0.54         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.54           | ~ (v1_relat_1 @ X0)
% 0.20/0.54           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))))
% 0.20/0.54         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '23'])).
% 0.20/0.54  thf('25', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.54         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['19'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.20/0.54         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.20/0.54         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.54  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.54         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.54       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.54      inference('split', [status(esa)], ['19'])).
% 0.20/0.54  thf('34', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['24', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.20/0.54      inference('clc', [status(thm)], ['15', '35'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '36'])).
% 0.20/0.54  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.54  thf('39', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '39'])).
% 0.20/0.54  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.54  thf('42', plain, ($false), inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
