%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MUK3tEiiXl

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:20 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 102 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  489 ( 709 expanded)
%              Number of equality atoms :   44 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43
        = ( k1_tarski @ X42 ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X24: $i] :
      ( r1_xboole_0 @ X24 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(demod,[status(thm)],['15','22'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('30',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('35',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X31 != X30 )
      | ( r2_hidden @ X31 @ X32 )
      | ( X32
       != ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('36',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['41'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('43',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ X25 @ X26 )
      | ( ( k3_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
        = ( k3_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('50',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['2','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MUK3tEiiXl
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.09/1.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.09/1.29  % Solved by: fo/fo7.sh
% 1.09/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.09/1.29  % done 1484 iterations in 0.827s
% 1.09/1.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.09/1.29  % SZS output start Refutation
% 1.09/1.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.09/1.29  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.09/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.09/1.29  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.09/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.09/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.09/1.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.09/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.09/1.29  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.09/1.29  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.09/1.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.09/1.29  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.09/1.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.09/1.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.09/1.29  thf(t149_zfmisc_1, conjecture,
% 1.09/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.09/1.29     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.09/1.29         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.09/1.29       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.09/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.09/1.29    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.09/1.29        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.09/1.29            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.09/1.29          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.09/1.29    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.09/1.29  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf(commutativity_k2_xboole_0, axiom,
% 1.09/1.29    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.09/1.29  thf('1', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.09/1.29  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 1.09/1.29      inference('demod', [status(thm)], ['0', '1'])).
% 1.09/1.29  thf('3', plain,
% 1.09/1.29      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf(commutativity_k3_xboole_0, axiom,
% 1.09/1.29    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.09/1.29  thf('4', plain,
% 1.09/1.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.29  thf('5', plain,
% 1.09/1.29      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 1.09/1.29      inference('demod', [status(thm)], ['3', '4'])).
% 1.09/1.29  thf(l3_zfmisc_1, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.09/1.29       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.09/1.29  thf('6', plain,
% 1.09/1.29      (![X42 : $i, X43 : $i]:
% 1.09/1.29         (((X43) = (k1_tarski @ X42))
% 1.09/1.29          | ((X43) = (k1_xboole_0))
% 1.09/1.29          | ~ (r1_tarski @ X43 @ (k1_tarski @ X42)))),
% 1.09/1.29      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.09/1.29  thf('7', plain,
% 1.09/1.29      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.09/1.29        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D_1)))),
% 1.09/1.29      inference('sup-', [status(thm)], ['5', '6'])).
% 1.09/1.29  thf(t17_xboole_1, axiom,
% 1.09/1.29    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.09/1.29  thf('8', plain,
% 1.09/1.29      (![X21 : $i, X22 : $i]: (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ X21)),
% 1.09/1.29      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.09/1.29  thf('9', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf(d7_xboole_0, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.09/1.29       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.09/1.29  thf('10', plain,
% 1.09/1.29      (![X4 : $i, X5 : $i]:
% 1.09/1.29         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.09/1.29      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.09/1.29  thf('11', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['9', '10'])).
% 1.09/1.29  thf('12', plain,
% 1.09/1.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.29  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.09/1.29      inference('demod', [status(thm)], ['11', '12'])).
% 1.09/1.29  thf(t100_xboole_1, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.09/1.29  thf('14', plain,
% 1.09/1.29      (![X13 : $i, X14 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X13 @ X14)
% 1.09/1.29           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.09/1.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.09/1.29  thf('15', plain,
% 1.09/1.29      (((k4_xboole_0 @ sk_B @ sk_C_1) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['13', '14'])).
% 1.09/1.29  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.09/1.29  thf('16', plain, (![X24 : $i]: (r1_xboole_0 @ X24 @ k1_xboole_0)),
% 1.09/1.29      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.09/1.29  thf('17', plain,
% 1.09/1.29      (![X4 : $i, X5 : $i]:
% 1.09/1.29         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.09/1.29      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.09/1.29  thf('18', plain,
% 1.09/1.29      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['16', '17'])).
% 1.09/1.29  thf('19', plain,
% 1.09/1.29      (![X13 : $i, X14 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X13 @ X14)
% 1.09/1.29           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.09/1.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.09/1.29  thf('20', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['18', '19'])).
% 1.09/1.29  thf(t3_boole, axiom,
% 1.09/1.29    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.09/1.29  thf('21', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 1.09/1.29      inference('cnf', [status(esa)], [t3_boole])).
% 1.09/1.29  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['20', '21'])).
% 1.09/1.29  thf('23', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 1.09/1.29      inference('demod', [status(thm)], ['15', '22'])).
% 1.09/1.29  thf(t106_xboole_1, axiom,
% 1.09/1.29    (![A:$i,B:$i,C:$i]:
% 1.09/1.29     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.09/1.29       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.09/1.29  thf('24', plain,
% 1.09/1.29      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.09/1.29         ((r1_xboole_0 @ X15 @ X17)
% 1.09/1.29          | ~ (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 1.09/1.29      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.09/1.29  thf('25', plain,
% 1.09/1.29      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 1.09/1.29      inference('sup-', [status(thm)], ['23', '24'])).
% 1.09/1.29  thf('26', plain,
% 1.09/1.29      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_1)),
% 1.09/1.29      inference('sup-', [status(thm)], ['8', '25'])).
% 1.09/1.29  thf(symmetry_r1_xboole_0, axiom,
% 1.09/1.29    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.09/1.29  thf('27', plain,
% 1.09/1.29      (![X7 : $i, X8 : $i]:
% 1.09/1.29         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.09/1.29      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.09/1.29  thf('28', plain,
% 1.09/1.29      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['26', '27'])).
% 1.09/1.29  thf('29', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 1.09/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.29  thf(t3_xboole_0, axiom,
% 1.09/1.29    (![A:$i,B:$i]:
% 1.09/1.29     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.09/1.29            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.09/1.29       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.09/1.29            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.09/1.29  thf('30', plain,
% 1.09/1.29      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.09/1.29         (~ (r2_hidden @ X11 @ X9)
% 1.09/1.29          | ~ (r2_hidden @ X11 @ X12)
% 1.09/1.29          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.09/1.29      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.09/1.29  thf('31', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['29', '30'])).
% 1.09/1.29  thf('32', plain,
% 1.09/1.29      (![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['28', '31'])).
% 1.09/1.29  thf('33', plain,
% 1.09/1.29      ((~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))
% 1.09/1.29        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.09/1.29      inference('sup-', [status(thm)], ['7', '32'])).
% 1.09/1.29  thf(t69_enumset1, axiom,
% 1.09/1.29    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.09/1.29  thf('34', plain,
% 1.09/1.29      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.09/1.29      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.09/1.29  thf(d2_tarski, axiom,
% 1.09/1.29    (![A:$i,B:$i,C:$i]:
% 1.09/1.29     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.09/1.29       ( ![D:$i]:
% 1.09/1.29         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.09/1.29  thf('35', plain,
% 1.09/1.29      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.09/1.29         (((X31) != (X30))
% 1.09/1.29          | (r2_hidden @ X31 @ X32)
% 1.09/1.29          | ((X32) != (k2_tarski @ X33 @ X30)))),
% 1.09/1.29      inference('cnf', [status(esa)], [d2_tarski])).
% 1.09/1.29  thf('36', plain,
% 1.09/1.29      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 1.09/1.29      inference('simplify', [status(thm)], ['35'])).
% 1.09/1.29  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['34', '36'])).
% 1.09/1.29  thf('38', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.09/1.29      inference('demod', [status(thm)], ['33', '37'])).
% 1.09/1.29  thf('39', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.09/1.29      inference('demod', [status(thm)], ['11', '12'])).
% 1.09/1.29  thf('40', plain,
% 1.09/1.29      (![X4 : $i, X6 : $i]:
% 1.09/1.29         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.09/1.29      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.09/1.29  thf('41', plain,
% 1.09/1.29      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 1.09/1.29      inference('sup-', [status(thm)], ['39', '40'])).
% 1.09/1.29  thf('42', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.09/1.29      inference('simplify', [status(thm)], ['41'])).
% 1.09/1.29  thf(t78_xboole_1, axiom,
% 1.09/1.29    (![A:$i,B:$i,C:$i]:
% 1.09/1.29     ( ( r1_xboole_0 @ A @ B ) =>
% 1.09/1.29       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.09/1.29         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.09/1.29  thf('43', plain,
% 1.09/1.29      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.09/1.29         (~ (r1_xboole_0 @ X25 @ X26)
% 1.09/1.29          | ((k3_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 1.09/1.29              = (k3_xboole_0 @ X25 @ X27)))),
% 1.09/1.29      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.09/1.29  thf('44', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))
% 1.09/1.29           = (k3_xboole_0 @ sk_B @ X0))),
% 1.09/1.29      inference('sup-', [status(thm)], ['42', '43'])).
% 1.09/1.29  thf('45', plain,
% 1.09/1.29      (![X4 : $i, X6 : $i]:
% 1.09/1.29         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.09/1.29      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.09/1.29  thf('46', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.09/1.29          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 1.09/1.29      inference('sup-', [status(thm)], ['44', '45'])).
% 1.09/1.29  thf('47', plain,
% 1.09/1.29      ((((k1_xboole_0) != (k1_xboole_0))
% 1.09/1.29        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 1.09/1.29      inference('sup-', [status(thm)], ['38', '46'])).
% 1.09/1.29  thf('48', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 1.09/1.29      inference('simplify', [status(thm)], ['47'])).
% 1.09/1.29  thf('49', plain,
% 1.09/1.29      (![X7 : $i, X8 : $i]:
% 1.09/1.29         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.09/1.29      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.09/1.29  thf('50', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 1.09/1.29      inference('sup-', [status(thm)], ['48', '49'])).
% 1.09/1.29  thf('51', plain, ($false), inference('demod', [status(thm)], ['2', '50'])).
% 1.09/1.29  
% 1.09/1.29  % SZS output end Refutation
% 1.09/1.29  
% 1.09/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
