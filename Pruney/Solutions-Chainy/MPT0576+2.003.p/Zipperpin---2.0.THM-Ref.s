%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wIkHXROpfg

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:21 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  92 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  375 ( 711 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t180_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t180_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X16 @ X17 ) @ ( k10_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('24',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k10_relat_1 @ X19 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['23','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) @ ( k10_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','34'])).

thf('36',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['13','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wIkHXROpfg
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.43  % Solved by: fo/fo7.sh
% 1.20/1.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.43  % done 1940 iterations in 0.980s
% 1.20/1.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.43  % SZS output start Refutation
% 1.20/1.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.43  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.20/1.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.43  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.43  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.43  thf(sk_D_type, type, sk_D: $i).
% 1.20/1.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.20/1.43  thf(sk_C_type, type, sk_C: $i).
% 1.20/1.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.20/1.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.43  thf(t180_relat_1, conjecture,
% 1.20/1.43    (![A:$i,B:$i,C:$i]:
% 1.20/1.43     ( ( v1_relat_1 @ C ) =>
% 1.20/1.43       ( ![D:$i]:
% 1.20/1.43         ( ( v1_relat_1 @ D ) =>
% 1.20/1.43           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 1.20/1.43             ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ))).
% 1.20/1.43  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.43    (~( ![A:$i,B:$i,C:$i]:
% 1.20/1.43        ( ( v1_relat_1 @ C ) =>
% 1.20/1.43          ( ![D:$i]:
% 1.20/1.43            ( ( v1_relat_1 @ D ) =>
% 1.20/1.43              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 1.20/1.43                ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ) )),
% 1.20/1.43    inference('cnf.neg', [status(esa)], [t180_relat_1])).
% 1.20/1.43  thf('0', plain,
% 1.20/1.43      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(t39_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.20/1.43  thf('1', plain,
% 1.20/1.43      (![X9 : $i, X10 : $i]:
% 1.20/1.43         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.20/1.43           = (k2_xboole_0 @ X9 @ X10))),
% 1.20/1.43      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.20/1.43  thf(t7_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.20/1.43  thf('2', plain,
% 1.20/1.43      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 1.20/1.43      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.20/1.43  thf(t43_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i,C:$i]:
% 1.20/1.43     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.20/1.43       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.20/1.43  thf('3', plain,
% 1.20/1.43      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.20/1.43         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.20/1.43          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.20/1.43      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.20/1.43  thf('4', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.20/1.43      inference('sup-', [status(thm)], ['2', '3'])).
% 1.20/1.43  thf('5', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.20/1.43      inference('sup-', [status(thm)], ['2', '3'])).
% 1.20/1.43  thf(t38_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.20/1.43       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.20/1.43  thf('6', plain,
% 1.20/1.43      (![X7 : $i, X8 : $i]:
% 1.20/1.43         (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 1.20/1.43      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.20/1.43  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['5', '6'])).
% 1.20/1.43  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.20/1.43      inference('demod', [status(thm)], ['4', '7'])).
% 1.20/1.43  thf(t12_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.20/1.43  thf('9', plain,
% 1.20/1.43      (![X5 : $i, X6 : $i]:
% 1.20/1.43         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.20/1.43      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.20/1.43  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['8', '9'])).
% 1.20/1.43  thf('11', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.20/1.43      inference('sup+', [status(thm)], ['1', '10'])).
% 1.20/1.43  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.20/1.43      inference('sup-', [status(thm)], ['8', '9'])).
% 1.20/1.43  thf('13', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.20/1.43      inference('demod', [status(thm)], ['11', '12'])).
% 1.20/1.43  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(t10_xboole_1, axiom,
% 1.20/1.43    (![A:$i,B:$i,C:$i]:
% 1.20/1.43     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.20/1.43  thf('15', plain,
% 1.20/1.43      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.20/1.43         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 1.20/1.43      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.20/1.43  thf('16', plain,
% 1.20/1.43      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.20/1.43      inference('sup-', [status(thm)], ['14', '15'])).
% 1.20/1.43  thf('17', plain,
% 1.20/1.43      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.20/1.43         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.20/1.43          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.20/1.43      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.20/1.43  thf('18', plain,
% 1.20/1.43      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 1.20/1.43      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.43  thf('19', plain,
% 1.20/1.43      (![X5 : $i, X6 : $i]:
% 1.20/1.43         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.20/1.43      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.20/1.43  thf('20', plain,
% 1.20/1.43      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B) = (sk_B))),
% 1.20/1.43      inference('sup-', [status(thm)], ['18', '19'])).
% 1.20/1.43  thf(commutativity_k2_xboole_0, axiom,
% 1.20/1.43    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.20/1.43  thf('21', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.20/1.43      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.20/1.43  thf('22', plain,
% 1.20/1.43      (![X0 : $i]: ((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)) = (sk_B))),
% 1.20/1.43      inference('demod', [status(thm)], ['20', '21'])).
% 1.20/1.43  thf(t175_relat_1, axiom,
% 1.20/1.43    (![A:$i,B:$i,C:$i]:
% 1.20/1.43     ( ( v1_relat_1 @ C ) =>
% 1.20/1.43       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.20/1.43         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.20/1.43  thf('23', plain,
% 1.20/1.43      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.20/1.43         (((k10_relat_1 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.20/1.43            = (k2_xboole_0 @ (k10_relat_1 @ X16 @ X17) @ 
% 1.20/1.43               (k10_relat_1 @ X16 @ X18)))
% 1.20/1.43          | ~ (v1_relat_1 @ X16))),
% 1.20/1.43      inference('cnf', [status(esa)], [t175_relat_1])).
% 1.20/1.43  thf('24', plain, ((r1_tarski @ sk_C @ sk_D)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf(t179_relat_1, axiom,
% 1.20/1.43    (![A:$i,B:$i]:
% 1.20/1.43     ( ( v1_relat_1 @ B ) =>
% 1.20/1.43       ( ![C:$i]:
% 1.20/1.43         ( ( v1_relat_1 @ C ) =>
% 1.20/1.43           ( ( r1_tarski @ B @ C ) =>
% 1.20/1.43             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 1.20/1.43  thf('25', plain,
% 1.20/1.43      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.20/1.43         (~ (v1_relat_1 @ X19)
% 1.20/1.43          | (r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k10_relat_1 @ X19 @ X21))
% 1.20/1.43          | ~ (r1_tarski @ X20 @ X19)
% 1.20/1.43          | ~ (v1_relat_1 @ X20))),
% 1.20/1.43      inference('cnf', [status(esa)], [t179_relat_1])).
% 1.20/1.43  thf('26', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         (~ (v1_relat_1 @ sk_C)
% 1.20/1.43          | (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))
% 1.20/1.43          | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.43      inference('sup-', [status(thm)], ['24', '25'])).
% 1.20/1.43  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('29', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))),
% 1.20/1.43      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.20/1.43  thf('30', plain,
% 1.20/1.43      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.20/1.43         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 1.20/1.43      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.20/1.43  thf('31', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]:
% 1.20/1.43         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ 
% 1.20/1.43          (k2_xboole_0 @ X1 @ (k10_relat_1 @ sk_D @ X0)))),
% 1.20/1.43      inference('sup-', [status(thm)], ['29', '30'])).
% 1.20/1.43  thf('32', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]:
% 1.20/1.43         ((r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ 
% 1.20/1.43           (k10_relat_1 @ sk_D @ (k2_xboole_0 @ X1 @ X0)))
% 1.20/1.43          | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.43      inference('sup+', [status(thm)], ['23', '31'])).
% 1.20/1.43  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.43  thf('34', plain,
% 1.20/1.43      (![X0 : $i, X1 : $i]:
% 1.20/1.43         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ 
% 1.20/1.43          (k10_relat_1 @ sk_D @ (k2_xboole_0 @ X1 @ X0)))),
% 1.20/1.43      inference('demod', [status(thm)], ['32', '33'])).
% 1.20/1.43  thf('35', plain,
% 1.20/1.43      (![X0 : $i]:
% 1.20/1.43         (r1_tarski @ (k10_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)) @ 
% 1.20/1.43          (k10_relat_1 @ sk_D @ sk_B))),
% 1.20/1.43      inference('sup+', [status(thm)], ['22', '34'])).
% 1.20/1.43  thf('36', plain,
% 1.20/1.43      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 1.20/1.43      inference('sup+', [status(thm)], ['13', '35'])).
% 1.20/1.43  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 1.20/1.43  
% 1.20/1.43  % SZS output end Refutation
% 1.20/1.43  
% 1.20/1.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
