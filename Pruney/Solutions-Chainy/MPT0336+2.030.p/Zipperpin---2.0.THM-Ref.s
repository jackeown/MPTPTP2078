%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NDm0DKQ74G

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:24 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 113 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   23
%              Number of atoms          :  574 ( 842 expanded)
%              Number of equality atoms :   56 (  73 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X58: $i,X59: $i] :
      ( ( X59
        = ( k1_tarski @ X58 ) )
      | ( X59 = k1_xboole_0 )
      | ~ ( r1_tarski @ X59 @ ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
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

thf('32',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','35'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['48'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','53'])).

thf('55',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NDm0DKQ74G
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.74/1.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.74/1.96  % Solved by: fo/fo7.sh
% 1.74/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.96  % done 2227 iterations in 1.510s
% 1.74/1.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.74/1.96  % SZS output start Refutation
% 1.74/1.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.74/1.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.74/1.96  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.74/1.96  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.74/1.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.74/1.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(sk_D_type, type, sk_D: $i).
% 1.74/1.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.74/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.96  thf(t149_zfmisc_1, conjecture,
% 1.74/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.96     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.74/1.96         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.74/1.96       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.74/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.96        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.74/1.96            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.74/1.96          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.74/1.96    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.74/1.96  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(d7_xboole_0, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.74/1.96       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.74/1.96  thf('2', plain,
% 1.74/1.96      (![X2 : $i, X3 : $i]:
% 1.74/1.96         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.74/1.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.74/1.96  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.96  thf(commutativity_k3_xboole_0, axiom,
% 1.74/1.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.74/1.96  thf('4', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.74/1.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.74/1.96  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.74/1.96      inference('demod', [status(thm)], ['3', '4'])).
% 1.74/1.96  thf('6', plain,
% 1.74/1.96      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('7', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.74/1.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.74/1.96  thf('8', plain,
% 1.74/1.96      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.74/1.96      inference('demod', [status(thm)], ['6', '7'])).
% 1.74/1.96  thf(l3_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.74/1.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.74/1.96  thf('9', plain,
% 1.74/1.96      (![X58 : $i, X59 : $i]:
% 1.74/1.96         (((X59) = (k1_tarski @ X58))
% 1.74/1.96          | ((X59) = (k1_xboole_0))
% 1.74/1.96          | ~ (r1_tarski @ X59 @ (k1_tarski @ X58)))),
% 1.74/1.96      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.74/1.96  thf('10', plain,
% 1.74/1.96      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.74/1.96        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['8', '9'])).
% 1.74/1.96  thf('11', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.74/1.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.74/1.96  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.74/1.96      inference('demod', [status(thm)], ['3', '4'])).
% 1.74/1.96  thf(t16_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i,C:$i]:
% 1.74/1.96     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.74/1.96       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.74/1.96  thf('13', plain,
% 1.74/1.96      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 1.74/1.96           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.74/1.96  thf('14', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 1.74/1.96           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['12', '13'])).
% 1.74/1.96  thf(t17_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.74/1.96  thf('15', plain,
% 1.74/1.96      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 1.74/1.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.74/1.96  thf(t3_xboole_1, axiom,
% 1.74/1.96    (![A:$i]:
% 1.74/1.96     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.74/1.96  thf('16', plain,
% 1.74/1.96      (![X14 : $i]:
% 1.74/1.96         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.74/1.96  thf('17', plain,
% 1.74/1.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['15', '16'])).
% 1.74/1.96  thf('18', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.74/1.96      inference('demod', [status(thm)], ['14', '17'])).
% 1.74/1.96  thf('19', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.74/1.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.74/1.96  thf('20', plain,
% 1.74/1.96      (![X2 : $i, X4 : $i]:
% 1.74/1.96         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.74/1.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.74/1.96  thf('21', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.74/1.96      inference('sup-', [status(thm)], ['19', '20'])).
% 1.74/1.96  thf('22', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((k1_xboole_0) != (k1_xboole_0))
% 1.74/1.96          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 1.74/1.96      inference('sup-', [status(thm)], ['18', '21'])).
% 1.74/1.96  thf('23', plain,
% 1.74/1.96      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 1.74/1.96      inference('simplify', [status(thm)], ['22'])).
% 1.74/1.96  thf('24', plain,
% 1.74/1.96      (![X2 : $i, X3 : $i]:
% 1.74/1.96         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.74/1.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.74/1.96  thf('25', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B) = (k1_xboole_0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['23', '24'])).
% 1.74/1.96  thf('26', plain,
% 1.74/1.96      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 1.74/1.96           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.74/1.96  thf('27', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 1.74/1.96      inference('demod', [status(thm)], ['25', '26'])).
% 1.74/1.96  thf('28', plain,
% 1.74/1.96      (![X2 : $i, X4 : $i]:
% 1.74/1.96         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.74/1.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.74/1.96  thf('29', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((k1_xboole_0) != (k1_xboole_0))
% 1.74/1.96          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['27', '28'])).
% 1.74/1.96  thf('30', plain,
% 1.74/1.96      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.74/1.96      inference('simplify', [status(thm)], ['29'])).
% 1.74/1.96  thf('31', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(t3_xboole_0, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.74/1.96            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.74/1.96       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.74/1.96            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.74/1.96  thf('32', plain,
% 1.74/1.96      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.74/1.96         (~ (r2_hidden @ X7 @ X5)
% 1.74/1.96          | ~ (r2_hidden @ X7 @ X8)
% 1.74/1.96          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.74/1.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.74/1.96  thf('33', plain,
% 1.74/1.96      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['31', '32'])).
% 1.74/1.96  thf('34', plain,
% 1.74/1.96      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.74/1.96      inference('sup-', [status(thm)], ['30', '33'])).
% 1.74/1.96  thf('35', plain,
% 1.74/1.96      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['11', '34'])).
% 1.74/1.96  thf('36', plain,
% 1.74/1.96      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D))
% 1.74/1.96        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['10', '35'])).
% 1.74/1.96  thf(t69_enumset1, axiom,
% 1.74/1.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.74/1.96  thf('37', plain,
% 1.74/1.96      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 1.74/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.96  thf(t70_enumset1, axiom,
% 1.74/1.96    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.74/1.96  thf('38', plain,
% 1.74/1.96      (![X31 : $i, X32 : $i]:
% 1.74/1.96         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 1.74/1.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.74/1.96  thf(d1_enumset1, axiom,
% 1.74/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.74/1.96       ( ![E:$i]:
% 1.74/1.96         ( ( r2_hidden @ E @ D ) <=>
% 1.74/1.96           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.74/1.96  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.74/1.96  thf(zf_stmt_2, axiom,
% 1.74/1.96    (![E:$i,C:$i,B:$i,A:$i]:
% 1.74/1.96     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.74/1.96       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.74/1.96  thf(zf_stmt_3, axiom,
% 1.74/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.74/1.96       ( ![E:$i]:
% 1.74/1.96         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.74/1.96  thf('39', plain,
% 1.74/1.96      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.74/1.96         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 1.74/1.96          | (r2_hidden @ X23 @ X27)
% 1.74/1.96          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.74/1.96  thf('40', plain,
% 1.74/1.96      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.74/1.96         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 1.74/1.96          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 1.74/1.96      inference('simplify', [status(thm)], ['39'])).
% 1.74/1.96  thf('41', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.96         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.74/1.96          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.74/1.96      inference('sup+', [status(thm)], ['38', '40'])).
% 1.74/1.96  thf('42', plain,
% 1.74/1.96      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.74/1.96         (((X19) != (X18)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.74/1.96  thf('43', plain,
% 1.74/1.96      (![X18 : $i, X20 : $i, X21 : $i]:
% 1.74/1.96         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X18)),
% 1.74/1.96      inference('simplify', [status(thm)], ['42'])).
% 1.74/1.96  thf('44', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.74/1.96      inference('sup-', [status(thm)], ['41', '43'])).
% 1.74/1.96  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['37', '44'])).
% 1.74/1.96  thf('46', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.74/1.96      inference('demod', [status(thm)], ['36', '45'])).
% 1.74/1.96  thf('47', plain,
% 1.74/1.96      (![X2 : $i, X4 : $i]:
% 1.74/1.96         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.74/1.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.74/1.96  thf('48', plain,
% 1.74/1.96      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.74/1.96      inference('sup-', [status(thm)], ['46', '47'])).
% 1.74/1.96  thf('49', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.74/1.96      inference('simplify', [status(thm)], ['48'])).
% 1.74/1.96  thf(t78_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i,C:$i]:
% 1.74/1.96     ( ( r1_xboole_0 @ A @ B ) =>
% 1.74/1.96       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.74/1.96         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.74/1.96  thf('50', plain,
% 1.74/1.96      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.74/1.96         (~ (r1_xboole_0 @ X15 @ X16)
% 1.74/1.96          | ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.74/1.96              = (k3_xboole_0 @ X15 @ X17)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.74/1.96  thf('51', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 1.74/1.96           = (k3_xboole_0 @ sk_B @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['49', '50'])).
% 1.74/1.96  thf('52', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.74/1.96      inference('sup-', [status(thm)], ['19', '20'])).
% 1.74/1.96  thf('53', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.74/1.96          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.74/1.96      inference('sup-', [status(thm)], ['51', '52'])).
% 1.74/1.96  thf('54', plain,
% 1.74/1.96      ((((k1_xboole_0) != (k1_xboole_0))
% 1.74/1.96        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 1.74/1.96      inference('sup-', [status(thm)], ['5', '53'])).
% 1.74/1.96  thf('55', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.74/1.96      inference('simplify', [status(thm)], ['54'])).
% 1.74/1.96  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 1.74/1.96  
% 1.74/1.96  % SZS output end Refutation
% 1.74/1.96  
% 1.74/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
