%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fAJnRFXbwk

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:46 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 152 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  465 (1145 expanded)
%              Number of equality atoms :   27 (  70 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

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

thf('5',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X11 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','16'])).

thf('18',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('19',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('23',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_2 ) ) @ sk_B_2 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X20 ) @ X21 )
      | ( r2_hidden @ X20 @ ( k11_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_2 ) @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_2 ) @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
      & ( ( k11_relat_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','15'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k11_relat_1 @ X21 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['19'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['18','33','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['42','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_xboole_0 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['35','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fAJnRFXbwk
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 502 iterations in 0.286s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.52/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.52/0.72  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.52/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.72  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.52/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.72  thf(t7_xboole_0, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.72          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.52/0.72  thf(d1_xboole_0, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.72      inference('sup+', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf(t205_relat_1, conjecture,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ B ) =>
% 0.52/0.72       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.52/0.72         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i,B:$i]:
% 0.52/0.72        ( ( v1_relat_1 @ B ) =>
% 0.52/0.72          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.52/0.72            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))
% 0.52/0.72        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0)))
% 0.52/0.72         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('split', [status(esa)], ['5'])).
% 0.52/0.72  thf('7', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          (((X0) != (k1_xboole_0))
% 0.52/0.72           | ~ (v1_xboole_0 @ X0)
% 0.52/0.72           | ~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_2 @ sk_A))))
% 0.52/0.72         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['4', '6'])).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      (((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_2 @ sk_A))
% 0.52/0.72         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.52/0.72         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('simplify', [status(thm)], ['7'])).
% 0.52/0.72  thf('9', plain,
% 0.52/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.72  thf('10', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.52/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.72  thf(d3_tarski, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X3 @ X4)
% 0.52/0.72          | (r2_hidden @ X3 @ X5)
% 0.52/0.72          | ~ (r1_tarski @ X4 @ X5))),
% 0.52/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['9', '12'])).
% 0.52/0.72  thf(t64_zfmisc_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.52/0.72       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.72         (((X9) != (X11))
% 0.52/0.72          | ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11))))),
% 0.52/0.72      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      (![X10 : $i, X11 : $i]:
% 0.52/0.72         ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['14'])).
% 0.52/0.72  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['13', '15'])).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_2 @ sk_A)))
% 0.52/0.72         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['8', '16'])).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))) | 
% 0.52/0.72       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.52/0.72      inference('split', [status(esa)], ['5'])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.52/0.72        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))
% 0.52/0.72         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('split', [status(esa)], ['19'])).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.52/0.72      inference('split', [status(esa)], ['5'])).
% 0.52/0.72  thf(d4_relat_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.52/0.72       ( ![C:$i]:
% 0.52/0.72         ( ( r2_hidden @ C @ B ) <=>
% 0.52/0.72           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X17 @ X16)
% 0.52/0.72          | (r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.52/0.72          | ((X16) != (k1_relat_1 @ X15)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.72  thf('23', plain,
% 0.52/0.72      (![X15 : $i, X17 : $i]:
% 0.52/0.72         ((r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.52/0.72          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X15)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['22'])).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_2)) @ sk_B_2))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['21', '23'])).
% 0.52/0.72  thf(t204_relat_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ C ) =>
% 0.52/0.72       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.52/0.72         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.52/0.72  thf('25', plain,
% 0.52/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.72         (~ (r2_hidden @ (k4_tarski @ X22 @ X20) @ X21)
% 0.52/0.72          | (r2_hidden @ X20 @ (k11_relat_1 @ X21 @ X22))
% 0.52/0.72          | ~ (v1_relat_1 @ X21))),
% 0.52/0.72      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.52/0.72  thf('26', plain,
% 0.52/0.72      (((~ (v1_relat_1 @ sk_B_2)
% 0.52/0.72         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_2) @ 
% 0.52/0.72            (k11_relat_1 @ sk_B_2 @ sk_A))))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.72  thf('27', plain, ((v1_relat_1 @ sk_B_2)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('28', plain,
% 0.52/0.72      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_2) @ (k11_relat_1 @ sk_B_2 @ sk_A)))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.52/0.72      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.72  thf('30', plain,
% 0.52/0.72      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_2 @ sk_A)))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.72  thf('31', plain,
% 0.52/0.72      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) & 
% 0.52/0.72             (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['20', '30'])).
% 0.52/0.72  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['13', '15'])).
% 0.52/0.72  thf('33', plain,
% 0.52/0.72      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.52/0.72       ~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.72      inference('demod', [status(thm)], ['31', '32'])).
% 0.52/0.72  thf('34', plain, (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.72      inference('sat_resolution*', [status(thm)], ['18', '33'])).
% 0.52/0.72  thf('35', plain, (~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_2 @ sk_A))),
% 0.52/0.72      inference('simpl_trail', [status(thm)], ['17', '34'])).
% 0.52/0.72  thf('36', plain,
% 0.52/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X20 @ (k11_relat_1 @ X21 @ X22))
% 0.52/0.72          | (r2_hidden @ (k4_tarski @ X22 @ X20) @ X21)
% 0.52/0.72          | ~ (v1_relat_1 @ X21))),
% 0.52/0.72      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((v1_xboole_0 @ (k11_relat_1 @ X1 @ X0))
% 0.52/0.72          | ~ (v1_relat_1 @ X1)
% 0.52/0.72          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.52/0.72             X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.72  thf('39', plain,
% 0.52/0.72      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.72         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.52/0.72          | (r2_hidden @ X13 @ X16)
% 0.52/0.72          | ((X16) != (k1_relat_1 @ X15)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.72  thf('40', plain,
% 0.52/0.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.72         ((r2_hidden @ X13 @ (k1_relat_1 @ X15))
% 0.52/0.72          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.52/0.72      inference('simplify', [status(thm)], ['39'])).
% 0.52/0.72  thf('41', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X0)
% 0.52/0.72          | (v1_xboole_0 @ (k11_relat_1 @ X0 @ X1))
% 0.52/0.72          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['38', '40'])).
% 0.52/0.72  thf('42', plain,
% 0.52/0.72      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.52/0.72         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.52/0.72      inference('split', [status(esa)], ['19'])).
% 0.52/0.72  thf('43', plain,
% 0.52/0.72      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.52/0.72       (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.72      inference('split', [status(esa)], ['19'])).
% 0.52/0.72  thf('44', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.52/0.72      inference('sat_resolution*', [status(thm)], ['18', '33', '43'])).
% 0.52/0.72  thf('45', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.52/0.72      inference('simpl_trail', [status(thm)], ['42', '44'])).
% 0.52/0.72  thf('46', plain,
% 0.52/0.72      (((v1_xboole_0 @ (k11_relat_1 @ sk_B_2 @ sk_A)) | ~ (v1_relat_1 @ sk_B_2))),
% 0.52/0.72      inference('sup-', [status(thm)], ['41', '45'])).
% 0.52/0.72  thf('47', plain, ((v1_relat_1 @ sk_B_2)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('48', plain, ((v1_xboole_0 @ (k11_relat_1 @ sk_B_2 @ sk_A))),
% 0.52/0.72      inference('demod', [status(thm)], ['46', '47'])).
% 0.52/0.72  thf('49', plain, ($false), inference('demod', [status(thm)], ['35', '48'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
