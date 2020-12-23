%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c5qU5CzzpY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  458 ( 526 expanded)
%              Number of equality atoms :   47 (  55 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('21',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X49 ) )
        = ( k1_tarski @ X48 ) )
      | ( X48 = X49 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t29_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k2_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_zfmisc_1])).

thf('25',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c5qU5CzzpY
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 126 iterations in 0.064s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(t70_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf(t69_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('1', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(t71_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.20/0.53           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.20/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.53  thf(t74_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.53     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.53       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.20/0.53           = (k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39))),
% 0.20/0.53      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.20/0.53  thf(t73_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.53     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.53       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.53         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.20/0.53           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.20/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.53           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.53         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.20/0.53           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.20/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.53  thf(t61_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.53     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.53       ( k2_xboole_0 @
% 0.20/0.53         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.53           = (k2_xboole_0 @ (k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9) @ 
% 0.20/0.53              (k1_tarski @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.20/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.20/0.53              (k1_tarski @ X5)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.20/0.53              (k1_tarski @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.20/0.53  thf(t72_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.20/0.53           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.20/0.53              (k1_tarski @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.20/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['3', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.20/0.53           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 0.20/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['2', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.20/0.53           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.20/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.53           = (k2_tarski @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf(t20_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53         ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ( A ) != ( B ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X48 : $i, X49 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X49))
% 0.20/0.53            = (k1_tarski @ X48))
% 0.20/0.53          | ((X48) = (X49)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.53  thf(t98_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X2 @ X3)
% 0.20/0.53           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.53            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.20/0.53          | ((X0) = (X1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k2_tarski @ X1 @ X0)
% 0.20/0.53            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.20/0.53          | ((X0) = (X1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['20', '23'])).
% 0.20/0.53  thf(t29_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) != ( B ) ) =>
% 0.20/0.53       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53         ( k2_tarski @ A @ B ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( ( A ) != ( B ) ) =>
% 0.20/0.53          ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53            ( k2_tarski @ A @ B ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t29_zfmisc_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.53         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.20/0.53        | ((sk_B) = (sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain, (((sk_B) = (sk_A))),
% 0.20/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.53  thf('28', plain, (((sk_A) != (sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('29', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
