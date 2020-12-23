%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bhU2Zn4A9E

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:19 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 140 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  582 ( 992 expanded)
%              Number of equality atoms :   60 ( 109 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t51_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
          = ( k1_tarski @ B ) )
       => ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t51_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','10'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','23'])).

thf('25',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','23'])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('31',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('39',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ ( k3_tarski @ X51 ) )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['40','45'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X56 @ X55 )
      | ~ ( r1_tarski @ ( k2_tarski @ X54 @ X56 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ ( k3_tarski @ X51 ) )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('54',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X54 @ X55 )
      | ~ ( r1_tarski @ ( k2_tarski @ X54 @ X56 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['29','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bhU2Zn4A9E
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.85  % Solved by: fo/fo7.sh
% 0.65/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.85  % done 477 iterations in 0.397s
% 0.65/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.85  % SZS output start Refutation
% 0.65/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.65/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.85  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.65/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.65/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.65/0.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.65/0.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.65/0.85  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.65/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.85  thf(t51_zfmisc_1, conjecture,
% 0.65/0.85    (![A:$i,B:$i]:
% 0.65/0.85     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.65/0.85       ( r2_hidden @ B @ A ) ))).
% 0.65/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.85    (~( ![A:$i,B:$i]:
% 0.65/0.85        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.65/0.85          ( r2_hidden @ B @ A ) ) )),
% 0.65/0.85    inference('cnf.neg', [status(esa)], [t51_zfmisc_1])).
% 0.65/0.85  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('1', plain,
% 0.65/0.85      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf(t95_xboole_1, axiom,
% 0.65/0.85    (![A:$i,B:$i]:
% 0.65/0.85     ( ( k3_xboole_0 @ A @ B ) =
% 0.65/0.85       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.65/0.85  thf('2', plain,
% 0.65/0.85      (![X8 : $i, X9 : $i]:
% 0.65/0.85         ((k3_xboole_0 @ X8 @ X9)
% 0.65/0.85           = (k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X9)))),
% 0.65/0.85      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.65/0.85  thf(t91_xboole_1, axiom,
% 0.65/0.85    (![A:$i,B:$i,C:$i]:
% 0.65/0.85     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.65/0.85       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.65/0.85  thf('3', plain,
% 0.65/0.85      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.65/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.65/0.85           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.65/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.85  thf('4', plain,
% 0.65/0.85      (![X8 : $i, X9 : $i]:
% 0.65/0.85         ((k3_xboole_0 @ X8 @ X9)
% 0.65/0.85           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ (k2_xboole_0 @ X8 @ X9))))),
% 0.65/0.85      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.85  thf('5', plain,
% 0.65/0.85      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.65/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.65/0.85           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.65/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.85  thf(t92_xboole_1, axiom,
% 0.65/0.85    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.65/0.85  thf('6', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.65/0.85      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.65/0.85  thf('7', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.65/0.85           = (k1_xboole_0))),
% 0.65/0.85      inference('sup+', [status(thm)], ['5', '6'])).
% 0.65/0.85  thf('8', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         ((k5_xboole_0 @ X1 @ 
% 0.65/0.85           (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.65/0.85            (k3_xboole_0 @ X1 @ X0)))
% 0.65/0.85           = (k1_xboole_0))),
% 0.65/0.85      inference('sup+', [status(thm)], ['4', '7'])).
% 0.65/0.85  thf('9', plain,
% 0.65/0.85      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.65/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.65/0.85           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.65/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.85  thf('10', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         ((k5_xboole_0 @ X1 @ 
% 0.65/0.85           (k5_xboole_0 @ X0 @ 
% 0.65/0.85            (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))
% 0.65/0.85           = (k1_xboole_0))),
% 0.65/0.85      inference('demod', [status(thm)], ['8', '9'])).
% 0.65/0.85  thf('11', plain,
% 0.65/0.85      (((k5_xboole_0 @ sk_A @ 
% 0.65/0.85         (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.65/0.85          (k5_xboole_0 @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ 
% 0.65/0.85           (k1_tarski @ sk_B))))
% 0.65/0.85         = (k1_xboole_0))),
% 0.65/0.85      inference('sup+', [status(thm)], ['1', '10'])).
% 0.65/0.85  thf(commutativity_k5_xboole_0, axiom,
% 0.65/0.85    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.65/0.85  thf('12', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.65/0.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.85  thf('13', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.65/0.85      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.65/0.85  thf('14', plain,
% 0.65/0.85      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.65/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.65/0.85           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.65/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.85  thf('15', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.65/0.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.85      inference('sup+', [status(thm)], ['13', '14'])).
% 0.65/0.85  thf(idempotence_k2_xboole_0, axiom,
% 0.65/0.85    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.65/0.85  thf('16', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.65/0.85      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.65/0.85  thf('17', plain,
% 0.65/0.85      (![X8 : $i, X9 : $i]:
% 0.65/0.85         ((k3_xboole_0 @ X8 @ X9)
% 0.65/0.85           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ (k2_xboole_0 @ X8 @ X9))))),
% 0.65/0.85      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.85  thf('18', plain,
% 0.65/0.85      (![X0 : $i]:
% 0.65/0.85         ((k3_xboole_0 @ X0 @ X0)
% 0.65/0.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.65/0.85      inference('sup+', [status(thm)], ['16', '17'])).
% 0.65/0.85  thf(idempotence_k3_xboole_0, axiom,
% 0.65/0.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.65/0.85  thf('19', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.65/0.85      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.65/0.85  thf('20', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.65/0.85      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.65/0.85  thf('21', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.85      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.65/0.85  thf('22', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.65/0.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.85  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.85      inference('sup+', [status(thm)], ['21', '22'])).
% 0.65/0.85  thf('24', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.85      inference('demod', [status(thm)], ['15', '23'])).
% 0.65/0.85  thf('25', plain,
% 0.65/0.85      (((k5_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.85         = (k1_xboole_0))),
% 0.65/0.85      inference('demod', [status(thm)], ['11', '12', '24'])).
% 0.65/0.85  thf('26', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.85      inference('demod', [status(thm)], ['15', '23'])).
% 0.65/0.85  thf('27', plain,
% 0.65/0.85      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.65/0.85         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.65/0.85      inference('sup+', [status(thm)], ['25', '26'])).
% 0.65/0.85  thf('28', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.85      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.65/0.85  thf('29', plain, (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))),
% 0.65/0.85      inference('demod', [status(thm)], ['27', '28'])).
% 0.65/0.85  thf(t70_enumset1, axiom,
% 0.65/0.85    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.65/0.85  thf('30', plain,
% 0.65/0.85      (![X23 : $i, X24 : $i]:
% 0.65/0.85         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.65/0.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.85  thf(t69_enumset1, axiom,
% 0.65/0.85    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.65/0.85  thf('31', plain,
% 0.65/0.85      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.65/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.85  thf('32', plain,
% 0.65/0.85      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.65/0.85      inference('sup+', [status(thm)], ['30', '31'])).
% 0.65/0.85  thf(d1_enumset1, axiom,
% 0.65/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.85     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.65/0.85       ( ![E:$i]:
% 0.65/0.85         ( ( r2_hidden @ E @ D ) <=>
% 0.65/0.85           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.65/0.85  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.65/0.85  thf(zf_stmt_2, axiom,
% 0.65/0.85    (![E:$i,C:$i,B:$i,A:$i]:
% 0.65/0.85     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.65/0.85       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.65/0.85  thf(zf_stmt_3, axiom,
% 0.65/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.85     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.65/0.85       ( ![E:$i]:
% 0.65/0.85         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.65/0.85  thf('33', plain,
% 0.65/0.85      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.65/0.85         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.65/0.85          | (r2_hidden @ X15 @ X19)
% 0.65/0.85          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.65/0.85  thf('34', plain,
% 0.65/0.85      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.65/0.85         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.65/0.85          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.65/0.85      inference('simplify', [status(thm)], ['33'])).
% 0.65/0.85  thf('35', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.65/0.85          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.65/0.85      inference('sup+', [status(thm)], ['32', '34'])).
% 0.65/0.85  thf('36', plain,
% 0.65/0.85      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.65/0.85         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.65/0.85  thf('37', plain,
% 0.65/0.85      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.65/0.85         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 0.65/0.85      inference('simplify', [status(thm)], ['36'])).
% 0.65/0.85  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.65/0.85      inference('sup-', [status(thm)], ['35', '37'])).
% 0.65/0.85  thf(l49_zfmisc_1, axiom,
% 0.65/0.85    (![A:$i,B:$i]:
% 0.65/0.85     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.65/0.85  thf('39', plain,
% 0.65/0.85      (![X50 : $i, X51 : $i]:
% 0.65/0.85         ((r1_tarski @ X50 @ (k3_tarski @ X51)) | ~ (r2_hidden @ X50 @ X51))),
% 0.65/0.85      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.65/0.85  thf('40', plain,
% 0.65/0.85      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_tarski @ X0)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['38', '39'])).
% 0.65/0.85  thf('41', plain,
% 0.65/0.85      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.65/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.85  thf(l51_zfmisc_1, axiom,
% 0.65/0.85    (![A:$i,B:$i]:
% 0.65/0.85     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.65/0.85  thf('42', plain,
% 0.65/0.85      (![X52 : $i, X53 : $i]:
% 0.65/0.85         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.65/0.85      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.65/0.85  thf('43', plain,
% 0.65/0.85      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.65/0.85      inference('sup+', [status(thm)], ['41', '42'])).
% 0.65/0.85  thf('44', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.65/0.85      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.65/0.85  thf('45', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.65/0.85      inference('demod', [status(thm)], ['43', '44'])).
% 0.65/0.85  thf('46', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.65/0.85      inference('demod', [status(thm)], ['40', '45'])).
% 0.65/0.85  thf(t38_zfmisc_1, axiom,
% 0.65/0.85    (![A:$i,B:$i,C:$i]:
% 0.65/0.85     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.65/0.85       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.65/0.85  thf('47', plain,
% 0.65/0.85      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.65/0.85         ((r2_hidden @ X56 @ X55)
% 0.65/0.85          | ~ (r1_tarski @ (k2_tarski @ X54 @ X56) @ X55))),
% 0.65/0.85      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.65/0.85  thf('48', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.65/0.85      inference('sup-', [status(thm)], ['46', '47'])).
% 0.65/0.85  thf('49', plain,
% 0.65/0.85      (![X50 : $i, X51 : $i]:
% 0.65/0.85         ((r1_tarski @ X50 @ (k3_tarski @ X51)) | ~ (r2_hidden @ X50 @ X51))),
% 0.65/0.85      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.65/0.85  thf('50', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['48', '49'])).
% 0.65/0.85  thf('51', plain,
% 0.65/0.85      (![X52 : $i, X53 : $i]:
% 0.65/0.85         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.65/0.85      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.65/0.85  thf('52', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.65/0.85      inference('demod', [status(thm)], ['50', '51'])).
% 0.65/0.85  thf('53', plain,
% 0.65/0.85      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.65/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.85  thf('54', plain,
% 0.65/0.85      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.65/0.85         ((r2_hidden @ X54 @ X55)
% 0.65/0.85          | ~ (r1_tarski @ (k2_tarski @ X54 @ X56) @ X55))),
% 0.65/0.85      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.65/0.85  thf('55', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.65/0.85      inference('sup-', [status(thm)], ['53', '54'])).
% 0.65/0.85  thf('56', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['52', '55'])).
% 0.65/0.85  thf('57', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.65/0.85      inference('sup+', [status(thm)], ['29', '56'])).
% 0.65/0.85  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.65/0.85  
% 0.65/0.85  % SZS output end Refutation
% 0.65/0.85  
% 0.65/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
