%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7UzJsVPFM

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:34 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 112 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  461 ( 803 expanded)
%              Number of equality atoms :   27 (  46 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['9','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','12'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['18','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('31',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ sk_B_1 ) )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_B_1 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ X0 ) @ sk_B_1 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_C_2 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_B_1 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['35','38'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ sk_C_2 @ X0 ) @ sk_B_1 )
      | ( r1_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7UzJsVPFM
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.18/1.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.39  % Solved by: fo/fo7.sh
% 1.18/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.39  % done 2235 iterations in 0.914s
% 1.18/1.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.39  % SZS output start Refutation
% 1.18/1.39  thf(sk_B_type, type, sk_B: $i > $i).
% 1.18/1.39  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.18/1.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.18/1.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.18/1.39  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.18/1.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.18/1.39  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.18/1.39  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.18/1.39  thf(t63_xboole_1, conjecture,
% 1.18/1.39    (![A:$i,B:$i,C:$i]:
% 1.18/1.39     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.18/1.39       ( r1_xboole_0 @ A @ C ) ))).
% 1.18/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.39    (~( ![A:$i,B:$i,C:$i]:
% 1.18/1.39        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.18/1.39          ( r1_xboole_0 @ A @ C ) ) )),
% 1.18/1.39    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 1.18/1.39  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_2)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(t7_xboole_0, axiom,
% 1.18/1.39    (![A:$i]:
% 1.18/1.39     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.18/1.39          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.18/1.39  thf('1', plain,
% 1.18/1.39      (![X18 : $i]:
% 1.18/1.39         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 1.18/1.39      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.18/1.39  thf('2', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(t28_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.18/1.39  thf('3', plain,
% 1.18/1.39      (![X20 : $i, X21 : $i]:
% 1.18/1.39         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 1.18/1.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.18/1.39  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 1.18/1.39      inference('sup-', [status(thm)], ['2', '3'])).
% 1.18/1.39  thf(t48_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.18/1.39  thf('5', plain,
% 1.18/1.39      (![X22 : $i, X23 : $i]:
% 1.18/1.39         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.18/1.39           = (k3_xboole_0 @ X22 @ X23))),
% 1.18/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.39  thf(d5_xboole_0, axiom,
% 1.18/1.39    (![A:$i,B:$i,C:$i]:
% 1.18/1.39     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.18/1.39       ( ![D:$i]:
% 1.18/1.39         ( ( r2_hidden @ D @ C ) <=>
% 1.18/1.39           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.18/1.39  thf('6', plain,
% 1.18/1.39      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X6 @ X5)
% 1.18/1.39          | ~ (r2_hidden @ X6 @ X4)
% 1.18/1.39          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.18/1.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.18/1.39  thf('7', plain,
% 1.18/1.39      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X6 @ X4)
% 1.18/1.39          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.18/1.39      inference('simplify', [status(thm)], ['6'])).
% 1.18/1.39  thf('8', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.18/1.39          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['5', '7'])).
% 1.18/1.39  thf('9', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X0 @ sk_A)
% 1.18/1.39          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['4', '8'])).
% 1.18/1.39  thf('10', plain,
% 1.18/1.39      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X6 @ X5)
% 1.18/1.39          | (r2_hidden @ X6 @ X3)
% 1.18/1.39          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.18/1.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.18/1.39  thf('11', plain,
% 1.18/1.39      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.18/1.39         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.18/1.39      inference('simplify', [status(thm)], ['10'])).
% 1.18/1.39  thf('12', plain,
% 1.18/1.39      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.18/1.39      inference('clc', [status(thm)], ['9', '11'])).
% 1.18/1.39  thf('13', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['1', '12'])).
% 1.18/1.39  thf(t3_xboole_0, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.18/1.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.18/1.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.18/1.39            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.18/1.39  thf('14', plain,
% 1.18/1.39      (![X10 : $i, X11 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 1.18/1.39      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.18/1.39  thf('15', plain,
% 1.18/1.39      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X2 @ X3)
% 1.18/1.39          | (r2_hidden @ X2 @ X4)
% 1.18/1.39          | (r2_hidden @ X2 @ X5)
% 1.18/1.39          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.18/1.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.18/1.39  thf('16', plain,
% 1.18/1.39      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.18/1.39         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.18/1.39          | (r2_hidden @ X2 @ X4)
% 1.18/1.39          | ~ (r2_hidden @ X2 @ X3))),
% 1.18/1.39      inference('simplify', [status(thm)], ['15'])).
% 1.18/1.39  thf('17', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X0 @ X1)
% 1.18/1.39          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 1.18/1.39          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['14', '16'])).
% 1.18/1.39  thf('18', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0)
% 1.18/1.39          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 1.18/1.39          | (r1_xboole_0 @ sk_A @ X0))),
% 1.18/1.39      inference('sup+', [status(thm)], ['13', '17'])).
% 1.18/1.39  thf('19', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_2)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('20', plain,
% 1.18/1.39      (![X18 : $i]:
% 1.18/1.39         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 1.18/1.39      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.18/1.39  thf(t4_xboole_0, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.18/1.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.18/1.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.18/1.39            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.18/1.39  thf('21', plain,
% 1.18/1.39      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 1.18/1.39          | ~ (r1_xboole_0 @ X14 @ X17))),
% 1.18/1.39      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.18/1.39  thf('22', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['20', '21'])).
% 1.18/1.39  thf('23', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['19', '22'])).
% 1.18/1.39  thf('24', plain,
% 1.18/1.39      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 1.18/1.39          | ~ (r1_xboole_0 @ X14 @ X17))),
% 1.18/1.39      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.18/1.39  thf('25', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.18/1.39      inference('sup-', [status(thm)], ['23', '24'])).
% 1.18/1.39  thf('26', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_2)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.18/1.39      inference('demod', [status(thm)], ['25', '26'])).
% 1.18/1.39  thf('28', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 1.18/1.39      inference('clc', [status(thm)], ['18', '27'])).
% 1.18/1.39  thf('29', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_2)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(symmetry_r1_xboole_0, axiom,
% 1.18/1.39    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.18/1.39  thf('30', plain,
% 1.18/1.39      (![X8 : $i, X9 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 1.18/1.39      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.18/1.39  thf('31', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B_1)),
% 1.18/1.39      inference('sup-', [status(thm)], ['29', '30'])).
% 1.18/1.39  thf('32', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['20', '21'])).
% 1.18/1.39  thf('33', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B_1) = (k1_xboole_0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['31', '32'])).
% 1.18/1.39  thf(t51_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.18/1.39       ( A ) ))).
% 1.18/1.39  thf('34', plain,
% 1.18/1.39      (![X24 : $i, X25 : $i]:
% 1.18/1.39         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 1.18/1.39           = (X24))),
% 1.18/1.39      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.18/1.39  thf('35', plain,
% 1.18/1.39      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ sk_B_1))
% 1.18/1.39         = (sk_C_2))),
% 1.18/1.39      inference('sup+', [status(thm)], ['33', '34'])).
% 1.18/1.39  thf(commutativity_k2_xboole_0, axiom,
% 1.18/1.39    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.18/1.39  thf('36', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.18/1.39      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.18/1.39  thf(t1_boole, axiom,
% 1.18/1.39    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.18/1.39  thf('37', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.18/1.39      inference('cnf', [status(esa)], [t1_boole])).
% 1.18/1.39  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.18/1.39      inference('sup+', [status(thm)], ['36', '37'])).
% 1.18/1.39  thf('39', plain, (((k4_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_C_2))),
% 1.18/1.39      inference('demod', [status(thm)], ['35', '38'])).
% 1.18/1.39  thf('40', plain,
% 1.18/1.39      (![X10 : $i, X11 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X11))),
% 1.18/1.39      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.18/1.39  thf('41', plain,
% 1.18/1.39      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X6 @ X4)
% 1.18/1.39          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.18/1.39      inference('simplify', [status(thm)], ['6'])).
% 1.18/1.39  thf('42', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.18/1.39          | ~ (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['40', '41'])).
% 1.18/1.39  thf('43', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         (~ (r2_hidden @ (sk_C @ sk_C_2 @ X0) @ sk_B_1)
% 1.18/1.39          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_C_2 @ sk_B_1)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['39', '42'])).
% 1.18/1.39  thf('44', plain, (((k4_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_C_2))),
% 1.18/1.39      inference('demod', [status(thm)], ['35', '38'])).
% 1.18/1.39  thf('45', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         (~ (r2_hidden @ (sk_C @ sk_C_2 @ X0) @ sk_B_1)
% 1.18/1.39          | (r1_xboole_0 @ X0 @ sk_C_2))),
% 1.18/1.39      inference('demod', [status(thm)], ['43', '44'])).
% 1.18/1.39  thf('46', plain,
% 1.18/1.39      (((r1_xboole_0 @ sk_A @ sk_C_2) | (r1_xboole_0 @ sk_A @ sk_C_2))),
% 1.18/1.39      inference('sup-', [status(thm)], ['28', '45'])).
% 1.18/1.39  thf('47', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 1.18/1.39      inference('simplify', [status(thm)], ['46'])).
% 1.18/1.39  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 1.18/1.39  
% 1.18/1.39  % SZS output end Refutation
% 1.18/1.39  
% 1.18/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
