%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kB4DsQkTAn

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  332 ( 479 expanded)
%              Number of equality atoms :   32 (  56 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ sk_B @ sk_C )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ sk_B @ sk_C )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) )
      = ( k1_enumset1 @ X0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) @ ( k1_enumset1 @ X0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_C @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_C @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_C @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('24',plain,
    ( ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['16','21','24'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('27',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kB4DsQkTAn
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 269 iterations in 0.124s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.57  thf(t70_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i]:
% 0.20/0.57         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.20/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.57  thf(t69_enumset1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.57  thf('1', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.57  thf(t8_zfmisc_1, conjecture,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.57        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t8_zfmisc_1])).
% 0.20/0.57  thf('2', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(l53_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.57       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X1 @ X0 @ sk_B @ sk_C)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ sk_A)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X0 @ X0 @ sk_B @ sk_C)
% 0.20/0.57           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.57  thf(t71_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.20/0.57           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A))
% 0.20/0.57           = (k1_enumset1 @ X0 @ sk_B @ sk_C))),
% 0.20/0.57      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf(t40_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X8 : $i, X9 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.20/0.57           = (k4_xboole_0 @ X8 @ X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.57  thf(t36_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)) @ 
% 0.20/0.57          (k1_enumset1 @ X0 @ sk_B @ sk_C))),
% 0.20/0.57      inference('sup+', [status(thm)], ['7', '10'])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.20/0.57        (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.57      inference('sup+', [status(thm)], ['0', '11'])).
% 0.20/0.57  thf('13', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.20/0.57        (k1_tarski @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf(t44_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.20/0.57       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.57         ((r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.20/0.57          | ~ (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12))),
% 0.20/0.57      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      ((r1_tarski @ (k1_tarski @ sk_B) @ 
% 0.20/0.57        (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.57  thf('18', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k2_enumset1 @ sk_B @ sk_C @ X1 @ X0)
% 0.20/0.57           = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k2_enumset1 @ sk_B @ sk_C @ X0 @ X0)
% 0.20/0.57           = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k2_enumset1 @ sk_B @ sk_C @ X0 @ X0)
% 0.20/0.57           = (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.57  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.57  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A) = (k1_tarski @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.57  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['16', '21', '24'])).
% 0.20/0.57  thf(t6_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.20/0.57       ( ( A ) = ( B ) ) ))).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (![X26 : $i, X27 : $i]:
% 0.20/0.57         (((X27) = (X26))
% 0.20/0.57          | ~ (r1_tarski @ (k1_tarski @ X27) @ (k1_tarski @ X26)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.20/0.57  thf('27', plain, (((sk_B) = (sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.57  thf('28', plain, (((sk_A) != (sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('29', plain, ($false),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
