%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8QJlfo68f0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:45 EST 2020

% Result     : Theorem 56.81s
% Output     : Refutation 56.81s
% Verified   : 
% Statistics : Number of formulae       :   58 (  64 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  434 ( 479 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X56 ) @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
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

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ X52 @ ( k3_tarski @ X53 ) )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( r1_tarski @ X3 @ ( k3_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X15 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X56 ) @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ ( k5_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ ( k5_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8QJlfo68f0
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:57:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 56.81/57.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 56.81/57.04  % Solved by: fo/fo7.sh
% 56.81/57.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 56.81/57.04  % done 7138 iterations in 56.572s
% 56.81/57.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 56.81/57.04  % SZS output start Refutation
% 56.81/57.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 56.81/57.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 56.81/57.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 56.81/57.04  thf(sk_B_type, type, sk_B: $i).
% 56.81/57.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 56.81/57.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 56.81/57.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 56.81/57.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 56.81/57.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 56.81/57.04  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 56.81/57.04  thf(sk_A_type, type, sk_A: $i).
% 56.81/57.04  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 56.81/57.04  thf(t81_zfmisc_1, conjecture,
% 56.81/57.04    (![A:$i,B:$i]:
% 56.81/57.04     ( r1_tarski @
% 56.81/57.04       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 56.81/57.04       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 56.81/57.04  thf(zf_stmt_0, negated_conjecture,
% 56.81/57.04    (~( ![A:$i,B:$i]:
% 56.81/57.04        ( r1_tarski @
% 56.81/57.04          ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 56.81/57.04          ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 56.81/57.04    inference('cnf.neg', [status(esa)], [t81_zfmisc_1])).
% 56.81/57.04  thf('0', plain,
% 56.81/57.04      (~ (r1_tarski @ 
% 56.81/57.04          (k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)) @ 
% 56.81/57.04          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 56.81/57.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.81/57.04  thf(t94_xboole_1, axiom,
% 56.81/57.04    (![A:$i,B:$i]:
% 56.81/57.04     ( ( k2_xboole_0 @ A @ B ) =
% 56.81/57.04       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 56.81/57.04  thf('1', plain,
% 56.81/57.04      (![X11 : $i, X12 : $i]:
% 56.81/57.04         ((k2_xboole_0 @ X11 @ X12)
% 56.81/57.04           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 56.81/57.04              (k3_xboole_0 @ X11 @ X12)))),
% 56.81/57.04      inference('cnf', [status(esa)], [t94_xboole_1])).
% 56.81/57.04  thf(t91_xboole_1, axiom,
% 56.81/57.04    (![A:$i,B:$i,C:$i]:
% 56.81/57.04     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 56.81/57.04       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 56.81/57.04  thf('2', plain,
% 56.81/57.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 56.81/57.04         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 56.81/57.04           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 56.81/57.04      inference('cnf', [status(esa)], [t91_xboole_1])).
% 56.81/57.04  thf('3', plain,
% 56.81/57.04      (![X11 : $i, X12 : $i]:
% 56.81/57.04         ((k2_xboole_0 @ X11 @ X12)
% 56.81/57.04           = (k5_xboole_0 @ X11 @ 
% 56.81/57.04              (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X11 @ X12))))),
% 56.81/57.04      inference('demod', [status(thm)], ['1', '2'])).
% 56.81/57.04  thf(t7_xboole_1, axiom,
% 56.81/57.04    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 56.81/57.04  thf('4', plain,
% 56.81/57.04      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 56.81/57.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 56.81/57.04  thf(t79_zfmisc_1, axiom,
% 56.81/57.04    (![A:$i,B:$i]:
% 56.81/57.04     ( ( r1_tarski @ A @ B ) =>
% 56.81/57.04       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 56.81/57.04  thf('5', plain,
% 56.81/57.04      (![X56 : $i, X57 : $i]:
% 56.81/57.04         ((r1_tarski @ (k1_zfmisc_1 @ X56) @ (k1_zfmisc_1 @ X57))
% 56.81/57.04          | ~ (r1_tarski @ X56 @ X57))),
% 56.81/57.04      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 56.81/57.04  thf('6', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i]:
% 56.81/57.04         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 56.81/57.04          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.81/57.04      inference('sup-', [status(thm)], ['4', '5'])).
% 56.81/57.04  thf(t108_xboole_1, axiom,
% 56.81/57.04    (![A:$i,B:$i,C:$i]:
% 56.81/57.04     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 56.81/57.04  thf('7', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.81/57.04         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 56.81/57.04      inference('cnf', [status(esa)], [t108_xboole_1])).
% 56.81/57.04  thf('8', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.81/57.04         (r1_tarski @ (k3_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 56.81/57.04          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.81/57.04      inference('sup-', [status(thm)], ['6', '7'])).
% 56.81/57.04  thf(t70_enumset1, axiom,
% 56.81/57.04    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 56.81/57.04  thf('9', plain,
% 56.81/57.04      (![X25 : $i, X26 : $i]:
% 56.81/57.04         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 56.81/57.04      inference('cnf', [status(esa)], [t70_enumset1])).
% 56.81/57.04  thf(d1_enumset1, axiom,
% 56.81/57.04    (![A:$i,B:$i,C:$i,D:$i]:
% 56.81/57.04     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 56.81/57.04       ( ![E:$i]:
% 56.81/57.04         ( ( r2_hidden @ E @ D ) <=>
% 56.81/57.04           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 56.81/57.04  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 56.81/57.04  thf(zf_stmt_2, axiom,
% 56.81/57.04    (![E:$i,C:$i,B:$i,A:$i]:
% 56.81/57.04     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 56.81/57.04       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 56.81/57.04  thf(zf_stmt_3, axiom,
% 56.81/57.04    (![A:$i,B:$i,C:$i,D:$i]:
% 56.81/57.04     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 56.81/57.04       ( ![E:$i]:
% 56.81/57.04         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 56.81/57.04  thf('10', plain,
% 56.81/57.04      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 56.81/57.04         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 56.81/57.04          | (r2_hidden @ X18 @ X22)
% 56.81/57.04          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 56.81/57.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 56.81/57.04  thf('11', plain,
% 56.81/57.04      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 56.81/57.04         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 56.81/57.04          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 56.81/57.04      inference('simplify', [status(thm)], ['10'])).
% 56.81/57.04  thf(l49_zfmisc_1, axiom,
% 56.81/57.04    (![A:$i,B:$i]:
% 56.81/57.04     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 56.81/57.04  thf('12', plain,
% 56.81/57.04      (![X52 : $i, X53 : $i]:
% 56.81/57.04         ((r1_tarski @ X52 @ (k3_tarski @ X53)) | ~ (r2_hidden @ X52 @ X53))),
% 56.81/57.04      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 56.81/57.04  thf('13', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.81/57.04         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 56.81/57.04          | (r1_tarski @ X3 @ (k3_tarski @ (k1_enumset1 @ X2 @ X1 @ X0))))),
% 56.81/57.04      inference('sup-', [status(thm)], ['11', '12'])).
% 56.81/57.04  thf('14', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.81/57.04         ((r1_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 56.81/57.04          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 56.81/57.04      inference('sup+', [status(thm)], ['9', '13'])).
% 56.81/57.04  thf(l51_zfmisc_1, axiom,
% 56.81/57.04    (![A:$i,B:$i]:
% 56.81/57.04     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 56.81/57.04  thf('15', plain,
% 56.81/57.04      (![X54 : $i, X55 : $i]:
% 56.81/57.04         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 56.81/57.04      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 56.81/57.04  thf('16', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.81/57.04         ((r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 56.81/57.04          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 56.81/57.04      inference('demod', [status(thm)], ['14', '15'])).
% 56.81/57.04  thf('17', plain,
% 56.81/57.04      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 56.81/57.04         (((X14) != (X15)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 56.81/57.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 56.81/57.04  thf('18', plain,
% 56.81/57.04      (![X13 : $i, X15 : $i, X16 : $i]:
% 56.81/57.04         ~ (zip_tseitin_0 @ X15 @ X15 @ X16 @ X13)),
% 56.81/57.04      inference('simplify', [status(thm)], ['17'])).
% 56.81/57.04  thf('19', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 56.81/57.04      inference('sup-', [status(thm)], ['16', '18'])).
% 56.81/57.04  thf('20', plain,
% 56.81/57.04      (![X56 : $i, X57 : $i]:
% 56.81/57.04         ((r1_tarski @ (k1_zfmisc_1 @ X56) @ (k1_zfmisc_1 @ X57))
% 56.81/57.04          | ~ (r1_tarski @ X56 @ X57))),
% 56.81/57.04      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 56.81/57.04  thf('21', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i]:
% 56.81/57.04         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 56.81/57.04          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.81/57.04      inference('sup-', [status(thm)], ['19', '20'])).
% 56.81/57.04  thf(t110_xboole_1, axiom,
% 56.81/57.04    (![A:$i,B:$i,C:$i]:
% 56.81/57.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 56.81/57.04       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 56.81/57.04  thf('22', plain,
% 56.81/57.04      (![X3 : $i, X4 : $i, X5 : $i]:
% 56.81/57.04         (~ (r1_tarski @ X3 @ X4)
% 56.81/57.04          | ~ (r1_tarski @ X5 @ X4)
% 56.81/57.04          | (r1_tarski @ (k5_xboole_0 @ X3 @ X5) @ X4))),
% 56.81/57.04      inference('cnf', [status(esa)], [t110_xboole_1])).
% 56.81/57.04  thf('23', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.81/57.04         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 56.81/57.04           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 56.81/57.04          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 56.81/57.04      inference('sup-', [status(thm)], ['21', '22'])).
% 56.81/57.04  thf('24', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.81/57.04         (r1_tarski @ 
% 56.81/57.04          (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ 
% 56.81/57.04           (k3_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2)) @ 
% 56.81/57.04          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.81/57.04      inference('sup-', [status(thm)], ['8', '23'])).
% 56.81/57.04  thf('25', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i]:
% 56.81/57.04         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 56.81/57.04          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.81/57.04      inference('sup-', [status(thm)], ['4', '5'])).
% 56.81/57.04  thf('26', plain,
% 56.81/57.04      (![X3 : $i, X4 : $i, X5 : $i]:
% 56.81/57.04         (~ (r1_tarski @ X3 @ X4)
% 56.81/57.04          | ~ (r1_tarski @ X5 @ X4)
% 56.81/57.04          | (r1_tarski @ (k5_xboole_0 @ X3 @ X5) @ X4))),
% 56.81/57.04      inference('cnf', [status(esa)], [t110_xboole_1])).
% 56.81/57.04  thf('27', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.81/57.04         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 56.81/57.04           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 56.81/57.04          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 56.81/57.04      inference('sup-', [status(thm)], ['25', '26'])).
% 56.81/57.04  thf('28', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.81/57.04         (r1_tarski @ 
% 56.81/57.04          (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ 
% 56.81/57.04           (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ 
% 56.81/57.04            (k3_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2))) @ 
% 56.81/57.04          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.81/57.04      inference('sup-', [status(thm)], ['24', '27'])).
% 56.81/57.04  thf('29', plain,
% 56.81/57.04      (![X0 : $i, X1 : $i]:
% 56.81/57.04         (r1_tarski @ 
% 56.81/57.04          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 56.81/57.04          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.81/57.04      inference('sup+', [status(thm)], ['3', '28'])).
% 56.81/57.04  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 56.81/57.04  
% 56.81/57.04  % SZS output end Refutation
% 56.81/57.04  
% 56.81/57.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
