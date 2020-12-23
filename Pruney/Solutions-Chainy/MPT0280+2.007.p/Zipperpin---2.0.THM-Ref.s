%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jSuShk2cHh

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:45 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   64 (  85 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  448 ( 628 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t81_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
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

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X16 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ ( k3_tarski @ X54 ) )
      | ~ ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X57: $i,X58: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X57 ) @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k3_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k5_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    ! [X57: $i,X58: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X57 ) @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k5_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jSuShk2cHh
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 2.31/2.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.31/2.50  % Solved by: fo/fo7.sh
% 2.31/2.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.31/2.50  % done 1410 iterations in 2.050s
% 2.31/2.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.31/2.50  % SZS output start Refutation
% 2.31/2.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.31/2.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.31/2.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.31/2.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.31/2.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.31/2.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.31/2.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.31/2.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.31/2.50  thf(sk_B_type, type, sk_B: $i).
% 2.31/2.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.31/2.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.31/2.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.31/2.50  thf(sk_A_type, type, sk_A: $i).
% 2.31/2.50  thf(t81_zfmisc_1, conjecture,
% 2.31/2.50    (![A:$i,B:$i]:
% 2.31/2.50     ( r1_tarski @
% 2.31/2.50       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 2.31/2.50       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.31/2.50  thf(zf_stmt_0, negated_conjecture,
% 2.31/2.50    (~( ![A:$i,B:$i]:
% 2.31/2.50        ( r1_tarski @
% 2.31/2.50          ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 2.31/2.50          ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 2.31/2.50    inference('cnf.neg', [status(esa)], [t81_zfmisc_1])).
% 2.31/2.50  thf('0', plain,
% 2.31/2.50      (~ (r1_tarski @ 
% 2.31/2.50          (k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.31/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.50  thf(t98_xboole_1, axiom,
% 2.31/2.50    (![A:$i,B:$i]:
% 2.31/2.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.31/2.50  thf('1', plain,
% 2.31/2.50      (![X12 : $i, X13 : $i]:
% 2.31/2.50         ((k2_xboole_0 @ X12 @ X13)
% 2.31/2.50           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 2.31/2.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.31/2.50  thf(commutativity_k3_xboole_0, axiom,
% 2.31/2.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.31/2.50  thf('2', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.50  thf(t70_enumset1, axiom,
% 2.31/2.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.31/2.50  thf('3', plain,
% 2.31/2.50      (![X26 : $i, X27 : $i]:
% 2.31/2.50         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 2.31/2.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.31/2.50  thf(d1_enumset1, axiom,
% 2.31/2.50    (![A:$i,B:$i,C:$i,D:$i]:
% 2.31/2.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.31/2.50       ( ![E:$i]:
% 2.31/2.50         ( ( r2_hidden @ E @ D ) <=>
% 2.31/2.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.31/2.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.31/2.50  thf(zf_stmt_2, axiom,
% 2.31/2.50    (![E:$i,C:$i,B:$i,A:$i]:
% 2.31/2.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.31/2.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.31/2.50  thf(zf_stmt_3, axiom,
% 2.31/2.50    (![A:$i,B:$i,C:$i,D:$i]:
% 2.31/2.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.31/2.50       ( ![E:$i]:
% 2.31/2.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.31/2.50  thf('4', plain,
% 2.31/2.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.31/2.50         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 2.31/2.50          | (r2_hidden @ X19 @ X23)
% 2.31/2.50          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 2.31/2.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.31/2.50  thf('5', plain,
% 2.31/2.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 2.31/2.50         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 2.31/2.50          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 2.31/2.50      inference('simplify', [status(thm)], ['4'])).
% 2.31/2.50  thf('6', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.31/2.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.31/2.50      inference('sup+', [status(thm)], ['3', '5'])).
% 2.31/2.50  thf('7', plain,
% 2.31/2.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.31/2.50         (((X15) != (X16)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 2.31/2.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.31/2.50  thf('8', plain,
% 2.31/2.50      (![X14 : $i, X16 : $i, X17 : $i]:
% 2.31/2.50         ~ (zip_tseitin_0 @ X16 @ X16 @ X17 @ X14)),
% 2.31/2.50      inference('simplify', [status(thm)], ['7'])).
% 2.31/2.50  thf('9', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 2.31/2.50      inference('sup-', [status(thm)], ['6', '8'])).
% 2.31/2.50  thf(l49_zfmisc_1, axiom,
% 2.31/2.50    (![A:$i,B:$i]:
% 2.31/2.50     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 2.31/2.50  thf('10', plain,
% 2.31/2.50      (![X53 : $i, X54 : $i]:
% 2.31/2.50         ((r1_tarski @ X53 @ (k3_tarski @ X54)) | ~ (r2_hidden @ X53 @ X54))),
% 2.31/2.50      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 2.31/2.50  thf('11', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]:
% 2.31/2.50         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 2.31/2.50      inference('sup-', [status(thm)], ['9', '10'])).
% 2.31/2.50  thf(l51_zfmisc_1, axiom,
% 2.31/2.50    (![A:$i,B:$i]:
% 2.31/2.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.31/2.50  thf('12', plain,
% 2.31/2.50      (![X55 : $i, X56 : $i]:
% 2.31/2.50         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 2.31/2.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.31/2.50  thf('13', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.31/2.50      inference('demod', [status(thm)], ['11', '12'])).
% 2.31/2.50  thf(t79_zfmisc_1, axiom,
% 2.31/2.50    (![A:$i,B:$i]:
% 2.31/2.50     ( ( r1_tarski @ A @ B ) =>
% 2.31/2.50       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.31/2.50  thf('14', plain,
% 2.31/2.50      (![X57 : $i, X58 : $i]:
% 2.31/2.50         ((r1_tarski @ (k1_zfmisc_1 @ X57) @ (k1_zfmisc_1 @ X58))
% 2.31/2.50          | ~ (r1_tarski @ X57 @ X58))),
% 2.31/2.50      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 2.31/2.50  thf('15', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]:
% 2.31/2.50         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('sup-', [status(thm)], ['13', '14'])).
% 2.31/2.50  thf(t108_xboole_1, axiom,
% 2.31/2.50    (![A:$i,B:$i,C:$i]:
% 2.31/2.50     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 2.31/2.50  thf('16', plain,
% 2.31/2.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.31/2.50         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ (k3_xboole_0 @ X4 @ X6) @ X5))),
% 2.31/2.50      inference('cnf', [status(esa)], [t108_xboole_1])).
% 2.31/2.50  thf('17', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.50         (r1_tarski @ (k3_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('sup-', [status(thm)], ['15', '16'])).
% 2.31/2.50  thf('18', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.50         (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_zfmisc_1 @ X0)) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X2 @ X0)))),
% 2.31/2.50      inference('sup+', [status(thm)], ['2', '17'])).
% 2.31/2.50  thf('19', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]:
% 2.31/2.50         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('sup-', [status(thm)], ['13', '14'])).
% 2.31/2.50  thf(t110_xboole_1, axiom,
% 2.31/2.50    (![A:$i,B:$i,C:$i]:
% 2.31/2.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.31/2.50       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 2.31/2.50  thf('20', plain,
% 2.31/2.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.31/2.50         (~ (r1_tarski @ X7 @ X8)
% 2.31/2.50          | ~ (r1_tarski @ X9 @ X8)
% 2.31/2.50          | (r1_tarski @ (k5_xboole_0 @ X7 @ X9) @ X8))),
% 2.31/2.50      inference('cnf', [status(esa)], [t110_xboole_1])).
% 2.31/2.50  thf('21', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.50         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 2.31/2.50           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.31/2.50          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.31/2.50      inference('sup-', [status(thm)], ['19', '20'])).
% 2.31/2.50  thf('22', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.50         (r1_tarski @ 
% 2.31/2.50          (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ 
% 2.31/2.50           (k3_xboole_0 @ X2 @ (k1_zfmisc_1 @ X0))) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('sup-', [status(thm)], ['18', '21'])).
% 2.31/2.50  thf('23', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.50  thf(t100_xboole_1, axiom,
% 2.31/2.50    (![A:$i,B:$i]:
% 2.31/2.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.31/2.50  thf('24', plain,
% 2.31/2.50      (![X2 : $i, X3 : $i]:
% 2.31/2.50         ((k4_xboole_0 @ X2 @ X3)
% 2.31/2.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 2.31/2.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.31/2.50  thf('25', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]:
% 2.31/2.50         ((k4_xboole_0 @ X0 @ X1)
% 2.31/2.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('sup+', [status(thm)], ['23', '24'])).
% 2.31/2.50  thf('26', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.50         (r1_tarski @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('demod', [status(thm)], ['22', '25'])).
% 2.31/2.50  thf(t7_xboole_1, axiom,
% 2.31/2.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.31/2.50  thf('27', plain,
% 2.31/2.50      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 2.31/2.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.31/2.50  thf('28', plain,
% 2.31/2.50      (![X57 : $i, X58 : $i]:
% 2.31/2.50         ((r1_tarski @ (k1_zfmisc_1 @ X57) @ (k1_zfmisc_1 @ X58))
% 2.31/2.50          | ~ (r1_tarski @ X57 @ X58))),
% 2.31/2.50      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 2.31/2.50  thf('29', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]:
% 2.31/2.50         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('sup-', [status(thm)], ['27', '28'])).
% 2.31/2.50  thf('30', plain,
% 2.31/2.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.31/2.50         (~ (r1_tarski @ X7 @ X8)
% 2.31/2.50          | ~ (r1_tarski @ X9 @ X8)
% 2.31/2.50          | (r1_tarski @ (k5_xboole_0 @ X7 @ X9) @ X8))),
% 2.31/2.50      inference('cnf', [status(esa)], [t110_xboole_1])).
% 2.31/2.50  thf('31', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.50         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 2.31/2.50           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.31/2.50          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.31/2.50      inference('sup-', [status(thm)], ['29', '30'])).
% 2.31/2.50  thf('32', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.50         (r1_tarski @ 
% 2.31/2.50          (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ 
% 2.31/2.50           (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2)) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('sup-', [status(thm)], ['26', '31'])).
% 2.31/2.50  thf('33', plain,
% 2.31/2.50      (![X0 : $i, X1 : $i]:
% 2.31/2.50         (r1_tarski @ 
% 2.31/2.50          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 2.31/2.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.31/2.50      inference('sup+', [status(thm)], ['1', '32'])).
% 2.31/2.50  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 2.31/2.50  
% 2.31/2.50  % SZS output end Refutation
% 2.31/2.50  
% 2.31/2.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
