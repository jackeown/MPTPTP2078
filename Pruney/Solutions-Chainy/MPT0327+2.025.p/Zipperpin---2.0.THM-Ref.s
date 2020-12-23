%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5DTkEhSAMD

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:53 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 104 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  478 ( 703 expanded)
%              Number of equality atoms :   47 (  68 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('18',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('28',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,(
    r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','45'])).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['23','50'])).

thf('52',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['2','15','16','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5DTkEhSAMD
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 273 iterations in 0.086s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(t140_zfmisc_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r2_hidden @ A @ B ) =>
% 0.36/0.55       ( ( k2_xboole_0 @
% 0.36/0.55           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.36/0.55         ( B ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i]:
% 0.36/0.55        ( ( r2_hidden @ A @ B ) =>
% 0.36/0.55          ( ( k2_xboole_0 @
% 0.36/0.55              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.36/0.55            ( B ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.36/0.55         (k1_tarski @ sk_A)) != (sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.36/0.55         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf(t3_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.36/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.55  thf(d5_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X6 @ X5)
% 0.36/0.55          | ~ (r2_hidden @ X6 @ X4)
% 0.36/0.55          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.36/0.55          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.36/0.55          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.55          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '7'])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.36/0.55  thf(t83_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 0.36/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.55           = (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf(t98_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X23 @ X24)
% 0.36/0.55           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.55           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X23 @ X24)
% 0.36/0.55           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.55           = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.55  thf('17', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(l1_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X35 : $i, X37 : $i]:
% 0.36/0.55         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.36/0.55      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.55  thf('19', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.55  thf(l32_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X12 : $i, X14 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.36/0.55          | ~ (r1_tarski @ X12 @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X23 @ X24)
% 0.36/0.55           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.36/0.55         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.55  thf(t1_boole, axiom,
% 0.36/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.55  thf('25', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.55  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf(t36_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.36/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X12 : $i, X14 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.36/0.55          | ~ (r1_tarski @ X12 @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X23 @ X24)
% 0.36/0.55           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.55           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.55           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['26', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.36/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.55  thf('35', plain, ((r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.36/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X12 : $i, X14 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.36/0.55          | ~ (r1_tarski @ X12 @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.36/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.55  thf('39', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X12 : $i, X14 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.36/0.55          | ~ (r1_tarski @ X12 @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X23 @ X24)
% 0.36/0.55           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.36/0.55         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      (((k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['32', '45'])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X23 @ X24)
% 0.36/0.55           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['46', '47'])).
% 0.36/0.55  thf('49', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.55  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['48', '49'])).
% 0.36/0.55  thf('51', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['23', '50'])).
% 0.36/0.55  thf('52', plain, (((sk_B) != (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '15', '16', '51'])).
% 0.36/0.55  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
