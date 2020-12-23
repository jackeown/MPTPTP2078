%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CQlKLmd6YJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:46 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 134 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  561 (1031 expanded)
%              Number of equality atoms :   54 ( 108 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['28','31'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
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

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('41',plain,(
    ! [X73: $i,X74: $i] :
      ( ( r1_tarski @ X73 @ ( k3_tarski @ X74 ) )
      | ~ ( r2_hidden @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['32','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CQlKLmd6YJ
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:34:29 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.82/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.00  % Solved by: fo/fo7.sh
% 0.82/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.00  % done 876 iterations in 0.557s
% 0.82/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.00  % SZS output start Refutation
% 0.82/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.00  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.82/1.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.82/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.82/1.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.82/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.00  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.82/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.82/1.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.00  thf(t63_zfmisc_1, conjecture,
% 0.82/1.00    (![A:$i,B:$i,C:$i]:
% 0.82/1.00     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.82/1.00       ( r2_hidden @ A @ C ) ))).
% 0.82/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.00    (~( ![A:$i,B:$i,C:$i]:
% 0.82/1.00        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.82/1.00          ( r2_hidden @ A @ C ) ) )),
% 0.82/1.00    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.82/1.00  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.82/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.00  thf('1', plain,
% 0.82/1.00      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.82/1.00         = (k2_tarski @ sk_A @ sk_B))),
% 0.82/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.00  thf(t92_xboole_1, axiom,
% 0.82/1.00    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.82/1.00  thf('2', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.82/1.00      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.82/1.00  thf(t95_xboole_1, axiom,
% 0.82/1.00    (![A:$i,B:$i]:
% 0.82/1.00     ( ( k3_xboole_0 @ A @ B ) =
% 0.82/1.00       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.82/1.00  thf('3', plain,
% 0.82/1.00      (![X12 : $i, X13 : $i]:
% 0.82/1.00         ((k3_xboole_0 @ X12 @ X13)
% 0.82/1.00           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 0.82/1.00              (k2_xboole_0 @ X12 @ X13)))),
% 0.82/1.00      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.82/1.00  thf(t91_xboole_1, axiom,
% 0.82/1.00    (![A:$i,B:$i,C:$i]:
% 0.82/1.00     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.82/1.00       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.82/1.00  thf('4', plain,
% 0.82/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.82/1.00           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.82/1.00      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.82/1.00  thf('5', plain,
% 0.82/1.00      (![X12 : $i, X13 : $i]:
% 0.82/1.00         ((k3_xboole_0 @ X12 @ X13)
% 0.82/1.00           = (k5_xboole_0 @ X12 @ 
% 0.82/1.00              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 0.82/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.82/1.00  thf('6', plain,
% 0.82/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.82/1.00           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.82/1.00      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.82/1.00  thf('7', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.82/1.00           = (k5_xboole_0 @ X1 @ 
% 0.82/1.00              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.82/1.00      inference('sup+', [status(thm)], ['5', '6'])).
% 0.82/1.00  thf('8', plain,
% 0.82/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.82/1.00           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.82/1.00      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.82/1.00  thf('9', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.82/1.00           = (k5_xboole_0 @ X1 @ 
% 0.82/1.00              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 0.82/1.00      inference('demod', [status(thm)], ['7', '8'])).
% 0.82/1.00  thf('10', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.82/1.00           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.82/1.00      inference('sup+', [status(thm)], ['2', '9'])).
% 0.82/1.00  thf(idempotence_k2_xboole_0, axiom,
% 0.82/1.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.82/1.00  thf('11', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.82/1.00      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.82/1.00  thf('12', plain,
% 0.82/1.00      (![X12 : $i, X13 : $i]:
% 0.82/1.00         ((k3_xboole_0 @ X12 @ X13)
% 0.82/1.00           = (k5_xboole_0 @ X12 @ 
% 0.82/1.00              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 0.82/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.82/1.00  thf('13', plain,
% 0.82/1.00      (![X0 : $i]:
% 0.82/1.00         ((k3_xboole_0 @ X0 @ X0)
% 0.82/1.00           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.82/1.00      inference('sup+', [status(thm)], ['11', '12'])).
% 0.82/1.00  thf(idempotence_k3_xboole_0, axiom,
% 0.82/1.00    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.82/1.00  thf('14', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.82/1.00      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.82/1.00  thf('15', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.82/1.00      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.82/1.00  thf('16', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.82/1.00      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.82/1.00  thf('17', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.82/1.00           = (k5_xboole_0 @ X1 @ X0))),
% 0.82/1.00      inference('demod', [status(thm)], ['10', '16'])).
% 0.82/1.00  thf('18', plain,
% 0.82/1.00      (((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.82/1.00         (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.82/1.00         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.82/1.00      inference('sup+', [status(thm)], ['1', '17'])).
% 0.82/1.00  thf(commutativity_k5_xboole_0, axiom,
% 0.82/1.00    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.82/1.00  thf('19', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.82/1.00      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.82/1.00  thf('20', plain,
% 0.82/1.00      (((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.82/1.00         (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.82/1.00         = (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.82/1.00      inference('demod', [status(thm)], ['18', '19'])).
% 0.82/1.00  thf('21', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.82/1.00      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.82/1.00  thf('22', plain,
% 0.82/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.82/1.00           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.82/1.00      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.82/1.00  thf('23', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]:
% 0.82/1.00         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.82/1.00           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.82/1.00      inference('sup+', [status(thm)], ['21', '22'])).
% 0.82/1.00  thf('24', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.82/1.00      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.82/1.00  thf('25', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.82/1.00      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.82/1.00  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.00      inference('sup+', [status(thm)], ['24', '25'])).
% 0.82/1.00  thf('27', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]:
% 0.82/1.00         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.82/1.00      inference('demod', [status(thm)], ['23', '26'])).
% 0.82/1.00  thf('28', plain,
% 0.82/1.00      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.82/1.00         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.82/1.00            (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.82/1.00      inference('sup+', [status(thm)], ['20', '27'])).
% 0.82/1.00  thf('29', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.82/1.00      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.82/1.00  thf('30', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]:
% 0.82/1.00         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.82/1.00      inference('demod', [status(thm)], ['23', '26'])).
% 0.82/1.00  thf('31', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]:
% 0.82/1.00         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.82/1.00      inference('sup+', [status(thm)], ['29', '30'])).
% 0.82/1.00  thf('32', plain,
% 0.82/1.00      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))),
% 0.82/1.00      inference('demod', [status(thm)], ['28', '31'])).
% 0.82/1.00  thf(t70_enumset1, axiom,
% 0.82/1.00    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.82/1.00  thf('33', plain,
% 0.82/1.00      (![X46 : $i, X47 : $i]:
% 0.82/1.00         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 0.82/1.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.00  thf(d1_enumset1, axiom,
% 0.82/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.00     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.82/1.00       ( ![E:$i]:
% 0.82/1.00         ( ( r2_hidden @ E @ D ) <=>
% 0.82/1.00           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.82/1.00  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.82/1.00  thf(zf_stmt_2, axiom,
% 0.82/1.00    (![E:$i,C:$i,B:$i,A:$i]:
% 0.82/1.00     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.82/1.00       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.82/1.00  thf(zf_stmt_3, axiom,
% 0.82/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.00     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.82/1.00       ( ![E:$i]:
% 0.82/1.00         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.82/1.00  thf('34', plain,
% 0.82/1.00      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.82/1.00         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.82/1.00          | (r2_hidden @ X19 @ X23)
% 0.82/1.00          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.82/1.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.00  thf('35', plain,
% 0.82/1.00      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.82/1.00         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.82/1.00          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.82/1.00      inference('simplify', [status(thm)], ['34'])).
% 0.82/1.00  thf('36', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.00         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.82/1.00          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.82/1.00      inference('sup+', [status(thm)], ['33', '35'])).
% 0.82/1.00  thf('37', plain,
% 0.82/1.00      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.82/1.00         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.82/1.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.00  thf('38', plain,
% 0.82/1.00      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.82/1.00         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.82/1.00      inference('simplify', [status(thm)], ['37'])).
% 0.82/1.00  thf('39', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.82/1.00      inference('sup-', [status(thm)], ['36', '38'])).
% 0.82/1.00  thf('40', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.82/1.00      inference('sup-', [status(thm)], ['36', '38'])).
% 0.82/1.00  thf(l49_zfmisc_1, axiom,
% 0.82/1.00    (![A:$i,B:$i]:
% 0.82/1.00     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.82/1.00  thf('41', plain,
% 0.82/1.00      (![X73 : $i, X74 : $i]:
% 0.82/1.00         ((r1_tarski @ X73 @ (k3_tarski @ X74)) | ~ (r2_hidden @ X73 @ X74))),
% 0.82/1.00      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.82/1.00  thf('42', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]:
% 0.82/1.00         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.82/1.00      inference('sup-', [status(thm)], ['40', '41'])).
% 0.82/1.00  thf(l51_zfmisc_1, axiom,
% 0.82/1.00    (![A:$i,B:$i]:
% 0.82/1.00     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.82/1.00  thf('43', plain,
% 0.82/1.00      (![X75 : $i, X76 : $i]:
% 0.82/1.00         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 0.82/1.00      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.82/1.00  thf('44', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.82/1.00      inference('demod', [status(thm)], ['42', '43'])).
% 0.82/1.00  thf(d3_tarski, axiom,
% 0.82/1.00    (![A:$i,B:$i]:
% 0.82/1.00     ( ( r1_tarski @ A @ B ) <=>
% 0.82/1.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.82/1.00  thf('45', plain,
% 0.82/1.00      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.00         (~ (r2_hidden @ X2 @ X3)
% 0.82/1.00          | (r2_hidden @ X2 @ X4)
% 0.82/1.00          | ~ (r1_tarski @ X3 @ X4))),
% 0.82/1.00      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.00  thf('46', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.00         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.82/1.00      inference('sup-', [status(thm)], ['44', '45'])).
% 0.82/1.00  thf('47', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.00         (r2_hidden @ X1 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.82/1.00      inference('sup-', [status(thm)], ['39', '46'])).
% 0.82/1.00  thf('48', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.82/1.00      inference('sup+', [status(thm)], ['32', '47'])).
% 0.82/1.00  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.82/1.00  
% 0.82/1.00  % SZS output end Refutation
% 0.82/1.00  
% 0.82/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
