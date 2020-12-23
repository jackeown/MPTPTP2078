%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8c5vElYEig

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:24 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 109 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  549 ( 816 expanded)
%              Number of equality atoms :   54 (  71 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X56: $i,X57: $i] :
      ( ( X57
        = ( k1_tarski @ X56 ) )
      | ( X57 = k1_xboole_0 )
      | ~ ( r1_tarski @ X57 @ ( k1_tarski @ X56 ) ) ) ),
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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
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

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','50'])).

thf('52',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8c5vElYEig
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:42:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.31/2.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.31/2.54  % Solved by: fo/fo7.sh
% 2.31/2.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.31/2.54  % done 4030 iterations in 2.088s
% 2.31/2.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.31/2.54  % SZS output start Refutation
% 2.31/2.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.31/2.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.31/2.54  thf(sk_D_type, type, sk_D: $i).
% 2.31/2.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.31/2.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.31/2.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.31/2.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.31/2.54  thf(sk_A_type, type, sk_A: $i).
% 2.31/2.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.31/2.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.31/2.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.31/2.54  thf(sk_B_type, type, sk_B: $i).
% 2.31/2.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.31/2.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.31/2.54  thf(t149_zfmisc_1, conjecture,
% 2.31/2.54    (![A:$i,B:$i,C:$i,D:$i]:
% 2.31/2.54     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.31/2.54         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.31/2.54       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.31/2.54  thf(zf_stmt_0, negated_conjecture,
% 2.31/2.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.31/2.54        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.31/2.54            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.31/2.54          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.31/2.54    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.31/2.54  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.31/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.54  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.31/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.54  thf(d7_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.31/2.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.31/2.54  thf('2', plain,
% 2.31/2.54      (![X2 : $i, X3 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.31/2.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.31/2.54  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 2.31/2.54      inference('sup-', [status(thm)], ['1', '2'])).
% 2.31/2.54  thf(commutativity_k3_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.31/2.54  thf('4', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.31/2.54      inference('demod', [status(thm)], ['3', '4'])).
% 2.31/2.54  thf('6', plain,
% 2.31/2.54      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 2.31/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.54  thf('7', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('8', plain,
% 2.31/2.54      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 2.31/2.54      inference('demod', [status(thm)], ['6', '7'])).
% 2.31/2.54  thf(l3_zfmisc_1, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 2.31/2.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 2.31/2.54  thf('9', plain,
% 2.31/2.54      (![X56 : $i, X57 : $i]:
% 2.31/2.54         (((X57) = (k1_tarski @ X56))
% 2.31/2.54          | ((X57) = (k1_xboole_0))
% 2.31/2.54          | ~ (r1_tarski @ X57 @ (k1_tarski @ X56)))),
% 2.31/2.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.31/2.54  thf('10', plain,
% 2.31/2.54      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 2.31/2.54        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D)))),
% 2.31/2.54      inference('sup-', [status(thm)], ['8', '9'])).
% 2.31/2.54  thf('11', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.31/2.54      inference('demod', [status(thm)], ['3', '4'])).
% 2.31/2.54  thf(t16_xboole_1, axiom,
% 2.31/2.54    (![A:$i,B:$i,C:$i]:
% 2.31/2.54     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.31/2.54       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.31/2.54  thf('13', plain,
% 2.31/2.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.31/2.54         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 2.31/2.54           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.31/2.54  thf('14', plain,
% 2.31/2.54      (![X0 : $i]:
% 2.31/2.54         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.31/2.54           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['12', '13'])).
% 2.31/2.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.31/2.54  thf('15', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 2.31/2.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.31/2.54  thf('16', plain,
% 2.31/2.54      (![X2 : $i, X3 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.31/2.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.31/2.54  thf('17', plain,
% 2.31/2.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.31/2.54      inference('sup-', [status(thm)], ['15', '16'])).
% 2.31/2.54  thf('18', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('19', plain,
% 2.31/2.54      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['17', '18'])).
% 2.31/2.54  thf('20', plain,
% 2.31/2.54      (![X0 : $i]:
% 2.31/2.54         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 2.31/2.54      inference('demod', [status(thm)], ['14', '19'])).
% 2.31/2.54  thf('21', plain,
% 2.31/2.54      (![X0 : $i]:
% 2.31/2.54         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['11', '20'])).
% 2.31/2.54  thf('22', plain,
% 2.31/2.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.31/2.54         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 2.31/2.54           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.31/2.54  thf('23', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('24', plain,
% 2.31/2.54      (![X2 : $i, X4 : $i]:
% 2.31/2.54         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 2.31/2.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.31/2.54  thf('25', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('sup-', [status(thm)], ['23', '24'])).
% 2.31/2.54  thf('26', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 2.31/2.54          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 2.31/2.54      inference('sup-', [status(thm)], ['22', '25'])).
% 2.31/2.54  thf('27', plain,
% 2.31/2.54      (![X0 : $i]:
% 2.31/2.54         (((k1_xboole_0) != (k1_xboole_0))
% 2.31/2.54          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0)))),
% 2.31/2.54      inference('sup-', [status(thm)], ['21', '26'])).
% 2.31/2.54  thf('28', plain,
% 2.31/2.54      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 2.31/2.54      inference('simplify', [status(thm)], ['27'])).
% 2.31/2.54  thf('29', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 2.31/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.54  thf(t3_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.31/2.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.31/2.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.31/2.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.31/2.54  thf('30', plain,
% 2.31/2.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.31/2.54         (~ (r2_hidden @ X7 @ X5)
% 2.31/2.54          | ~ (r2_hidden @ X7 @ X8)
% 2.31/2.54          | ~ (r1_xboole_0 @ X5 @ X8))),
% 2.31/2.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.31/2.54  thf('31', plain,
% 2.31/2.54      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.31/2.54      inference('sup-', [status(thm)], ['29', '30'])).
% 2.31/2.54  thf('32', plain,
% 2.31/2.54      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 2.31/2.54      inference('sup-', [status(thm)], ['28', '31'])).
% 2.31/2.54  thf('33', plain,
% 2.31/2.54      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D))
% 2.31/2.54        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 2.31/2.54      inference('sup-', [status(thm)], ['10', '32'])).
% 2.31/2.54  thf(t69_enumset1, axiom,
% 2.31/2.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.31/2.54  thf('34', plain,
% 2.31/2.54      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 2.31/2.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.31/2.54  thf(t70_enumset1, axiom,
% 2.31/2.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.31/2.54  thf('35', plain,
% 2.31/2.54      (![X29 : $i, X30 : $i]:
% 2.31/2.54         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 2.31/2.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.31/2.54  thf(d1_enumset1, axiom,
% 2.31/2.54    (![A:$i,B:$i,C:$i,D:$i]:
% 2.31/2.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.31/2.54       ( ![E:$i]:
% 2.31/2.54         ( ( r2_hidden @ E @ D ) <=>
% 2.31/2.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.31/2.54  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.31/2.54  thf(zf_stmt_2, axiom,
% 2.31/2.54    (![E:$i,C:$i,B:$i,A:$i]:
% 2.31/2.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.31/2.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.31/2.54  thf(zf_stmt_3, axiom,
% 2.31/2.54    (![A:$i,B:$i,C:$i,D:$i]:
% 2.31/2.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.31/2.54       ( ![E:$i]:
% 2.31/2.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.31/2.54  thf('36', plain,
% 2.31/2.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.31/2.54         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 2.31/2.54          | (r2_hidden @ X21 @ X25)
% 2.31/2.54          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 2.31/2.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.31/2.54  thf('37', plain,
% 2.31/2.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.31/2.54         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 2.31/2.54          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 2.31/2.54      inference('simplify', [status(thm)], ['36'])).
% 2.31/2.54  thf('38', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.54         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.31/2.54          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.31/2.54      inference('sup+', [status(thm)], ['35', '37'])).
% 2.31/2.54  thf('39', plain,
% 2.31/2.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.31/2.54         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 2.31/2.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.31/2.54  thf('40', plain,
% 2.31/2.54      (![X16 : $i, X18 : $i, X19 : $i]:
% 2.31/2.54         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 2.31/2.54      inference('simplify', [status(thm)], ['39'])).
% 2.31/2.54  thf('41', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.31/2.54      inference('sup-', [status(thm)], ['38', '40'])).
% 2.31/2.54  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['34', '41'])).
% 2.31/2.54  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 2.31/2.54      inference('demod', [status(thm)], ['33', '42'])).
% 2.31/2.54  thf('44', plain,
% 2.31/2.54      (![X2 : $i, X4 : $i]:
% 2.31/2.54         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 2.31/2.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.31/2.54  thf('45', plain,
% 2.31/2.54      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 2.31/2.54      inference('sup-', [status(thm)], ['43', '44'])).
% 2.31/2.54  thf('46', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.31/2.54      inference('simplify', [status(thm)], ['45'])).
% 2.31/2.54  thf(t78_xboole_1, axiom,
% 2.31/2.54    (![A:$i,B:$i,C:$i]:
% 2.31/2.54     ( ( r1_xboole_0 @ A @ B ) =>
% 2.31/2.54       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 2.31/2.54         ( k3_xboole_0 @ A @ C ) ) ))).
% 2.31/2.54  thf('47', plain,
% 2.31/2.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.31/2.54         (~ (r1_xboole_0 @ X13 @ X14)
% 2.31/2.54          | ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 2.31/2.54              = (k3_xboole_0 @ X13 @ X15)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t78_xboole_1])).
% 2.31/2.54  thf('48', plain,
% 2.31/2.54      (![X0 : $i]:
% 2.31/2.54         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 2.31/2.54           = (k3_xboole_0 @ sk_B @ X0))),
% 2.31/2.54      inference('sup-', [status(thm)], ['46', '47'])).
% 2.31/2.54  thf('49', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('sup-', [status(thm)], ['23', '24'])).
% 2.31/2.54  thf('50', plain,
% 2.31/2.54      (![X0 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 2.31/2.54          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 2.31/2.54      inference('sup-', [status(thm)], ['48', '49'])).
% 2.31/2.54  thf('51', plain,
% 2.31/2.54      ((((k1_xboole_0) != (k1_xboole_0))
% 2.31/2.54        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 2.31/2.54      inference('sup-', [status(thm)], ['5', '50'])).
% 2.31/2.54  thf('52', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.31/2.54      inference('simplify', [status(thm)], ['51'])).
% 2.31/2.54  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 2.31/2.54  
% 2.31/2.54  % SZS output end Refutation
% 2.31/2.54  
% 2.31/2.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
