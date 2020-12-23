%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IIGNQRD4ih

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 118 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  390 ( 962 expanded)
%              Number of equality atoms :   26 (  67 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

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
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
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
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k11_relat_1 @ X28 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ X29 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ k1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('12',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('19',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ ( k11_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['15','27','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['13','29'])).

thf('31',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('35',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['15','27'])).

thf('36',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IIGNQRD4ih
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 99 iterations in 0.042s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(t2_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.22/0.50       ( ( A ) = ( B ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((X1) = (X0))
% 0.22/0.50          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.22/0.50          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_tarski])).
% 0.22/0.50  thf(t2_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.50  thf(t4_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.22/0.50          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.50  thf('4', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.50  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.50  thf(t204_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X27 @ (k11_relat_1 @ X28 @ X29))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X29 @ X27) @ X28)
% 0.22/0.50          | ~ (v1_relat_1 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k4_tarski @ X0 @ (sk_C @ k1_xboole_0 @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.22/0.50             X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf(d4_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.50         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 0.22/0.50          | (r2_hidden @ X18 @ X21)
% 0.22/0.50          | ((X21) != (k1_relat_1 @ X20)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.50         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.22/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.50          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.50  thf(t205_relat_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.50         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( v1_relat_1 @ B ) =>
% 0.22/0.50          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.50            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.22/0.50        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.22/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.22/0.50        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.50       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.50         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['12'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.22/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['14'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X22 @ X21)
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 0.22/0.50          | ((X21) != (k1_relat_1 @ X20)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X20 : $i, X22 : $i]:
% 0.22/0.50         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 0.22/0.50          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 0.22/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.50         (~ (r2_hidden @ (k4_tarski @ X29 @ X27) @ X28)
% 0.22/0.50          | (r2_hidden @ X27 @ (k11_relat_1 @ X28 @ X29))
% 0.22/0.50          | ~ (v1_relat_1 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (((~ (v1_relat_1 @ sk_B)
% 0.22/0.50         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.22/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.22/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.22/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.22/0.50             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['16', '24'])).
% 0.22/0.50  thf('26', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.22/0.50       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.22/0.50       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('split', [status(esa)], ['12'])).
% 0.22/0.50  thf('29', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['15', '27', '28'])).
% 0.22/0.50  thf('30', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['13', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '30'])).
% 0.22/0.50  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('33', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.22/0.50         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['14'])).
% 0.22/0.50  thf('35', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['15', '27'])).
% 0.22/0.50  thf('36', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['33', '36'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
