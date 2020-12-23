%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W3OxjyfU3p

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:25 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 105 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  385 ( 642 expanded)
%              Number of equality atoms :   47 (  72 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X16 @ X13 ) @ ( sk_D @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
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

thf('2',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('17',plain,(
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

thf('18',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_relat_1 @ X1 )
         != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('33',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W3OxjyfU3p
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.72  % Solved by: fo/fo7.sh
% 0.45/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.72  % done 617 iterations in 0.267s
% 0.45/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.72  % SZS output start Refutation
% 0.45/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.72  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.45/0.72  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.45/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.72  thf(d4_relat_1, axiom,
% 0.45/0.72    (![A:$i,B:$i]:
% 0.45/0.72     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.45/0.72       ( ![C:$i]:
% 0.45/0.72         ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.72           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.45/0.72  thf('0', plain,
% 0.45/0.72      (![X13 : $i, X16 : $i]:
% 0.45/0.72         (((X16) = (k1_relat_1 @ X13))
% 0.45/0.72          | (r2_hidden @ 
% 0.45/0.72             (k4_tarski @ (sk_C_1 @ X16 @ X13) @ (sk_D @ X16 @ X13)) @ X13)
% 0.45/0.72          | (r2_hidden @ (sk_C_1 @ X16 @ X13) @ X16))),
% 0.45/0.72      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.45/0.72  thf(t2_boole, axiom,
% 0.45/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.72  thf('1', plain,
% 0.45/0.72      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.72  thf(t4_xboole_0, axiom,
% 0.45/0.72    (![A:$i,B:$i]:
% 0.45/0.72     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.72            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.72  thf('2', plain,
% 0.45/0.72      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.45/0.72         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.45/0.72          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.45/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.72  thf('3', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.72  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.72  thf('4', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.45/0.72      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.72  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.45/0.72      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.72  thf('6', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.45/0.72          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['0', '5'])).
% 0.45/0.72  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.45/0.72      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.72  thf('8', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.72  thf(dt_k4_relat_1, axiom,
% 0.45/0.72    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.45/0.72  thf('9', plain,
% 0.45/0.72      (![X18 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X18)) | ~ (v1_relat_1 @ X18))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.45/0.72  thf(t37_relat_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ A ) =>
% 0.45/0.72       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.45/0.72         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.45/0.72  thf('10', plain,
% 0.45/0.72      (![X22 : $i]:
% 0.45/0.72         (((k1_relat_1 @ X22) = (k2_relat_1 @ (k4_relat_1 @ X22)))
% 0.45/0.72          | ~ (v1_relat_1 @ X22))),
% 0.45/0.72      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.45/0.72  thf(fc9_relat_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.45/0.72       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.72  thf('11', plain,
% 0.45/0.72      (![X21 : $i]:
% 0.45/0.72         (~ (v1_xboole_0 @ (k2_relat_1 @ X21))
% 0.45/0.72          | ~ (v1_relat_1 @ X21)
% 0.45/0.72          | (v1_xboole_0 @ X21))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.45/0.72  thf('12', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.72  thf('13', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['9', '12'])).
% 0.45/0.72  thf('14', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.45/0.72          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['13'])).
% 0.45/0.72  thf('15', plain,
% 0.45/0.72      (![X22 : $i]:
% 0.45/0.72         (((k1_relat_1 @ X22) = (k2_relat_1 @ (k4_relat_1 @ X22)))
% 0.45/0.72          | ~ (v1_relat_1 @ X22))),
% 0.45/0.72      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.45/0.72  thf(l13_xboole_0, axiom,
% 0.45/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.72  thf('16', plain,
% 0.45/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.72  thf('17', plain,
% 0.45/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.72  thf(t60_relat_1, conjecture,
% 0.45/0.72    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.72     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.72    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.72        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.45/0.72    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.45/0.72  thf('18', plain,
% 0.45/0.72      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.45/0.72        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('19', plain,
% 0.45/0.72      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.72         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('split', [status(esa)], ['18'])).
% 0.45/0.72  thf('20', plain,
% 0.45/0.72      ((![X0 : $i]:
% 0.45/0.72          (((k2_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.45/0.72         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['17', '19'])).
% 0.45/0.72  thf('21', plain,
% 0.45/0.72      ((![X0 : $i, X1 : $i]:
% 0.45/0.72          (((k2_relat_1 @ X1) != (X0))
% 0.45/0.72           | ~ (v1_xboole_0 @ X0)
% 0.45/0.72           | ~ (v1_xboole_0 @ X1)))
% 0.45/0.72         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['16', '20'])).
% 0.45/0.72  thf('22', plain,
% 0.45/0.72      ((![X1 : $i]:
% 0.45/0.72          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_relat_1 @ X1))))
% 0.45/0.72         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.72  thf('23', plain,
% 0.45/0.72      ((![X0 : $i]:
% 0.45/0.72          (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.45/0.72           | ~ (v1_relat_1 @ X0)
% 0.45/0.72           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))))
% 0.45/0.72         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['15', '22'])).
% 0.45/0.72  thf('24', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.72  thf('25', plain,
% 0.45/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.72  thf('26', plain,
% 0.45/0.72      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.72         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('split', [status(esa)], ['18'])).
% 0.45/0.72  thf('27', plain,
% 0.45/0.72      ((![X0 : $i]:
% 0.45/0.72          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.45/0.72         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.72  thf('28', plain,
% 0.45/0.72      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.45/0.72         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['24', '27'])).
% 0.45/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.72  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.72  thf('30', plain,
% 0.45/0.72      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.72         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.72      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.72  thf('31', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.45/0.72      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.72  thf('32', plain,
% 0.45/0.72      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.45/0.72       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.45/0.72      inference('split', [status(esa)], ['18'])).
% 0.45/0.72  thf('33', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.45/0.72      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.45/0.72  thf('34', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 0.45/0.72      inference('simpl_trail', [status(thm)], ['23', '33'])).
% 0.45/0.72  thf('35', plain,
% 0.45/0.72      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.45/0.72      inference('clc', [status(thm)], ['14', '34'])).
% 0.45/0.72  thf('36', plain,
% 0.45/0.72      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['8', '35'])).
% 0.45/0.72  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.72  thf(t113_zfmisc_1, axiom,
% 0.45/0.72    (![A:$i,B:$i]:
% 0.45/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.72  thf('38', plain,
% 0.45/0.72      (![X9 : $i, X10 : $i]:
% 0.45/0.72         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.45/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.72  thf('39', plain,
% 0.45/0.72      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.72  thf(fc6_relat_1, axiom,
% 0.45/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.72  thf('40', plain,
% 0.45/0.72      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.72  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.72      inference('sup+', [status(thm)], ['39', '40'])).
% 0.45/0.72  thf('42', plain, ($false),
% 0.45/0.72      inference('demod', [status(thm)], ['36', '37', '41'])).
% 0.45/0.72  
% 0.45/0.72  % SZS output end Refutation
% 0.45/0.72  
% 0.57/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
