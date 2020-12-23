%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8IwvlOxlk3

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:32 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   50 (  87 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  678 (1271 expanded)
%              Number of equality atoms :   49 (  93 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t80_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t80_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k6_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t80_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ X30 @ ( k2_xboole_0 @ X27 @ X29 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X27 ) @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t132_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
        & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_zfmisc_1])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X27 @ X29 ) @ X28 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('23',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('24',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('28',plain,(
    ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['20','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8IwvlOxlk3
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.85/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.85/1.08  % Solved by: fo/fo7.sh
% 0.85/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.08  % done 210 iterations in 0.626s
% 0.85/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.85/1.08  % SZS output start Refutation
% 0.85/1.08  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.85/1.08                                           $i > $i).
% 0.85/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.85/1.08  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.85/1.08  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.85/1.08  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.85/1.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.85/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.85/1.08  thf(t69_enumset1, axiom,
% 0.85/1.08    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.85/1.08  thf('0', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.85/1.08      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.85/1.08  thf(t72_enumset1, axiom,
% 0.85/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.08     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.85/1.08  thf('1', plain,
% 0.85/1.08      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.08         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 0.85/1.08           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.85/1.08      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.85/1.08  thf(t77_enumset1, axiom,
% 0.85/1.08    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.85/1.08  thf('2', plain,
% 0.85/1.08      (![X20 : $i, X21 : $i]:
% 0.85/1.08         ((k2_enumset1 @ X20 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.85/1.08      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.85/1.08  thf('3', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['1', '2'])).
% 0.85/1.08  thf(t80_enumset1, axiom,
% 0.85/1.08    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.85/1.08     ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E ) =
% 0.85/1.08       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.85/1.08  thf('4', plain,
% 0.85/1.08      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.85/1.08         ((k5_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.85/1.08           = (k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 0.85/1.08      inference('cnf', [status(esa)], [t80_enumset1])).
% 0.85/1.08  thf(t68_enumset1, axiom,
% 0.85/1.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.85/1.08     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.85/1.08       ( k2_xboole_0 @
% 0.85/1.08         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.85/1.08  thf('5', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.85/1.08         ((k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.85/1.08           = (k2_xboole_0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6) @ 
% 0.85/1.08              (k1_tarski @ X7)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.85/1.08  thf('6', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.85/1.08         ((k6_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.85/1.08           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.85/1.08              (k1_tarski @ X5)))),
% 0.85/1.08      inference('sup+', [status(thm)], ['4', '5'])).
% 0.85/1.08  thf('7', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.08         ((k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.85/1.08           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.85/1.08      inference('sup+', [status(thm)], ['3', '6'])).
% 0.85/1.08  thf(t75_enumset1, axiom,
% 0.85/1.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.85/1.08     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.85/1.08       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.85/1.08  thf('8', plain,
% 0.85/1.08      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.85/1.08         ((k6_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.85/1.08           = (k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19))),
% 0.85/1.08      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.85/1.08  thf('9', plain,
% 0.85/1.08      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.85/1.08         ((k5_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.85/1.08           = (k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 0.85/1.08      inference('cnf', [status(esa)], [t80_enumset1])).
% 0.85/1.08  thf('10', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.85/1.08         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.85/1.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['8', '9'])).
% 0.85/1.08  thf('11', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.08         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.85/1.08           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.85/1.08      inference('demod', [status(thm)], ['7', '10'])).
% 0.85/1.08  thf('12', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.85/1.08           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.85/1.08      inference('sup+', [status(thm)], ['0', '11'])).
% 0.85/1.08  thf('13', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['1', '2'])).
% 0.85/1.08  thf('14', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k2_tarski @ X0 @ X1)
% 0.85/1.08           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.85/1.08      inference('demod', [status(thm)], ['12', '13'])).
% 0.85/1.08  thf(t120_zfmisc_1, axiom,
% 0.85/1.08    (![A:$i,B:$i,C:$i]:
% 0.85/1.08     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.85/1.08         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.85/1.08       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.85/1.08         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.85/1.08  thf('15', plain,
% 0.85/1.08      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.85/1.08         ((k2_zfmisc_1 @ X30 @ (k2_xboole_0 @ X27 @ X29))
% 0.85/1.08           = (k2_xboole_0 @ (k2_zfmisc_1 @ X30 @ X27) @ 
% 0.85/1.08              (k2_zfmisc_1 @ X30 @ X29)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.85/1.08  thf(t132_zfmisc_1, conjecture,
% 0.85/1.08    (![A:$i,B:$i,C:$i]:
% 0.85/1.08     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.85/1.08         ( k2_xboole_0 @
% 0.85/1.08           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.85/1.08           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.85/1.08       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.85/1.08         ( k2_xboole_0 @
% 0.85/1.08           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.85/1.08           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 0.85/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.08    (~( ![A:$i,B:$i,C:$i]:
% 0.85/1.08        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.85/1.08            ( k2_xboole_0 @
% 0.85/1.08              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.85/1.08              ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.85/1.08          ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.85/1.08            ( k2_xboole_0 @
% 0.85/1.08              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.85/1.08              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )),
% 0.85/1.08    inference('cnf.neg', [status(esa)], [t132_zfmisc_1])).
% 0.85/1.08  thf('16', plain,
% 0.85/1.08      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.85/1.08              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))
% 0.85/1.08        | ((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08            != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.85/1.08                (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.85/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.08  thf('17', plain,
% 0.85/1.08      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.85/1.08              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))
% 0.85/1.08         <= (~
% 0.85/1.08             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.85/1.08                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.85/1.08      inference('split', [status(esa)], ['16'])).
% 0.85/1.08  thf('18', plain,
% 0.85/1.08      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08          != (k2_zfmisc_1 @ sk_C @ 
% 0.85/1.08              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))))
% 0.85/1.08         <= (~
% 0.85/1.08             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.85/1.08                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.85/1.08      inference('sup-', [status(thm)], ['15', '17'])).
% 0.85/1.08  thf('19', plain,
% 0.85/1.08      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08          != (k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.85/1.08         <= (~
% 0.85/1.08             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.85/1.08                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.85/1.08      inference('sup-', [status(thm)], ['14', '18'])).
% 0.85/1.08  thf('20', plain,
% 0.85/1.08      (($false)
% 0.85/1.08         <= (~
% 0.85/1.08             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.85/1.08                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.85/1.08      inference('simplify', [status(thm)], ['19'])).
% 0.85/1.08  thf('21', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k2_tarski @ X0 @ X1)
% 0.85/1.08           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.85/1.08      inference('demod', [status(thm)], ['12', '13'])).
% 0.85/1.08  thf('22', plain,
% 0.85/1.08      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.85/1.08         ((k2_zfmisc_1 @ (k2_xboole_0 @ X27 @ X29) @ X28)
% 0.85/1.08           = (k2_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 0.85/1.08              (k2_zfmisc_1 @ X29 @ X28)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.85/1.08  thf('23', plain,
% 0.85/1.08      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08          != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.85/1.08              (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))
% 0.85/1.08         <= (~
% 0.85/1.08             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.85/1.08                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.85/1.08      inference('split', [status(esa)], ['16'])).
% 0.85/1.08  thf('24', plain,
% 0.85/1.08      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08          != (k2_zfmisc_1 @ 
% 0.85/1.08              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ sk_C)))
% 0.85/1.08         <= (~
% 0.85/1.08             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.85/1.08                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.85/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.85/1.08  thf('25', plain,
% 0.85/1.08      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08          != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 0.85/1.08         <= (~
% 0.85/1.08             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.85/1.08                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.85/1.08      inference('sup-', [status(thm)], ['21', '24'])).
% 0.85/1.08  thf('26', plain,
% 0.85/1.08      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.85/1.08             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.85/1.08      inference('simplify', [status(thm)], ['25'])).
% 0.85/1.08  thf('27', plain,
% 0.85/1.08      (~
% 0.85/1.08       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.85/1.08             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))) | 
% 0.85/1.08       ~
% 0.85/1.08       (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.85/1.08          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.85/1.08             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.85/1.08      inference('split', [status(esa)], ['16'])).
% 0.85/1.08  thf('28', plain,
% 0.85/1.08      (~
% 0.85/1.08       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.85/1.08          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.85/1.08             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))),
% 0.85/1.08      inference('sat_resolution*', [status(thm)], ['26', '27'])).
% 0.85/1.08  thf('29', plain, ($false),
% 0.85/1.08      inference('simpl_trail', [status(thm)], ['20', '28'])).
% 0.85/1.08  
% 0.85/1.08  % SZS output end Refutation
% 0.85/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
