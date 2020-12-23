%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BgKzd2ue9N

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  60 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  424 ( 460 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t8_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t8_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k2_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X4 @ X4 @ X4 @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X4 @ X4 @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','23'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('25',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46 = X45 )
      | ~ ( r1_tarski @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('26',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BgKzd2ue9N
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:55:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 117 iterations in 0.057s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.51                                           $i > $i).
% 0.21/0.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(t8_zfmisc_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t8_zfmisc_1])).
% 0.21/0.51  thf('0', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t70_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.51  thf(t72_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.51         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.21/0.51           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.51  thf(t71_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.21/0.51           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.51  thf(t69_enumset1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.51  thf('6', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf(t75_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.51     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.51       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.51         ((k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.21/0.51           = (k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 0.21/0.51      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.21/0.51  thf(t74_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.51     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.51       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.51         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.21/0.51           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.21/0.51      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.51           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf(t73_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.51     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.51       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.51         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.21/0.51           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.21/0.51      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.51           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf(l75_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.51     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.51       ( k2_xboole_0 @
% 0.21/0.51         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 0.21/0.51         X16 : $i]:
% 0.21/0.51         ((k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.21/0.51           = (k2_xboole_0 @ (k2_enumset1 @ X9 @ X10 @ X11 @ X12) @ 
% 0.21/0.51              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.21/0.51  thf(t21_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.51  thf(t29_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ (k2_xboole_0 @ X4 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         (r1_tarski @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.21/0.51          (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (r1_tarski @ (k2_enumset1 @ X4 @ X4 @ X4 @ X4) @ 
% 0.21/0.51          (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['12', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.21/0.51           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (r1_tarski @ (k1_enumset1 @ X4 @ X4 @ X4) @ 
% 0.21/0.51          (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (r1_tarski @ (k1_tarski @ X0) @ (k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['7', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (r1_tarski @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['4', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '22'])).
% 0.21/0.51  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['0', '23'])).
% 0.21/0.51  thf(t6_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.51       ( ( A ) = ( B ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X45 : $i, X46 : $i]:
% 0.21/0.51         (((X46) = (X45))
% 0.21/0.51          | ~ (r1_tarski @ (k1_tarski @ X46) @ (k1_tarski @ X45)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.51  thf('26', plain, (((sk_B) = (sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, (((sk_A) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
