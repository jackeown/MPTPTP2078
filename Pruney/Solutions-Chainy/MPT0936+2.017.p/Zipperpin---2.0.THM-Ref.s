%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TnWP2EYjBy

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:25 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 146 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  389 (1081 expanded)
%              Number of equality atoms :   54 ( 155 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('0',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_mcart_1 @ X33 @ X34 @ X35 )
      = ( k4_tarski @ ( k4_tarski @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_tarski @ ( k4_tarski @ X24 @ X25 ) @ ( k4_tarski @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) )
        = X31 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 != X21 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X21 ) )
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) )
     != ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) )
     != ( k1_tarski @ X21 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X21: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X21 ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(clc,[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X21: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X21 ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('30',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TnWP2EYjBy
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 368 iterations in 0.123s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.40/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.57  thf(t97_mcart_1, conjecture,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( k1_relat_1 @
% 0.40/0.57         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.40/0.57       ( k1_tarski @ A ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.57        ( ( k1_relat_1 @
% 0.40/0.57            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.40/0.57          ( k1_tarski @ A ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      (((k1_relat_1 @ 
% 0.40/0.57         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))))
% 0.40/0.57         != (k1_tarski @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(d3_mcart_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.40/0.57         ((k3_mcart_1 @ X33 @ X34 @ X35)
% 0.40/0.57           = (k4_tarski @ (k4_tarski @ X33 @ X34) @ X35))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.40/0.57  thf(t69_enumset1, axiom,
% 0.40/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.57  thf('2', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.57  thf(t36_zfmisc_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.40/0.57         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.40/0.57       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.40/0.57         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X24) @ (k2_tarski @ X25 @ X26))
% 0.40/0.57           = (k2_tarski @ (k4_tarski @ X24 @ X25) @ (k4_tarski @ X24 @ X26)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.40/0.57  thf('4', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.40/0.57           = (k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X1 @ X0)))),
% 0.40/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.57  thf('5', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.40/0.57           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.40/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.57  thf(t195_relat_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.57          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.40/0.57               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      (![X31 : $i, X32 : $i]:
% 0.40/0.57         (((X31) = (k1_xboole_0))
% 0.40/0.57          | ((k1_relat_1 @ (k2_zfmisc_1 @ X31 @ X32)) = (X31))
% 0.40/0.57          | ((X32) = (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.40/0.57            = (k1_tarski @ X1))
% 0.40/0.57          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.40/0.57          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.57  thf(t20_zfmisc_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.57         ( k1_tarski @ A ) ) <=>
% 0.40/0.57       ( ( A ) != ( B ) ) ))).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      (![X21 : $i, X22 : $i]:
% 0.40/0.57         (((X22) != (X21))
% 0.40/0.57          | ((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X21))
% 0.40/0.57              != (k1_tarski @ X22)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      (![X21 : $i]:
% 0.40/0.57         ((k4_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))
% 0.40/0.57           != (k1_tarski @ X21))),
% 0.40/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.40/0.57  thf('11', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.57  thf(t11_setfam_1, axiom,
% 0.40/0.57    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.40/0.57  thf('12', plain, (![X28 : $i]: ((k1_setfam_1 @ (k1_tarski @ X28)) = (X28))),
% 0.40/0.57      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.57  thf('13', plain,
% 0.40/0.57      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.40/0.57  thf(t12_setfam_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (![X29 : $i, X30 : $i]:
% 0.40/0.57         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.40/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.57  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.57  thf(t100_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X21 : $i]:
% 0.40/0.57         ((k5_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))
% 0.40/0.57           != (k1_tarski @ X21))),
% 0.40/0.57      inference('demod', [status(thm)], ['10', '17'])).
% 0.40/0.57  thf(t21_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X2 : $i, X3 : $i]:
% 0.40/0.57         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.40/0.57      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.40/0.57           = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.40/0.57  thf(t46_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X4 : $i, X5 : $i]:
% 0.40/0.57         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.40/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.40/0.57  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.40/0.57  thf('24', plain, (![X21 : $i]: ((k1_xboole_0) != (k1_tarski @ X21))),
% 0.40/0.57      inference('demod', [status(thm)], ['18', '23'])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((k1_tarski @ X1) = (k1_xboole_0))
% 0.40/0.57          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.40/0.57              = (k1_tarski @ X1)))),
% 0.40/0.57      inference('clc', [status(thm)], ['8', '24'])).
% 0.40/0.57  thf('26', plain, (![X21 : $i]: ((k1_xboole_0) != (k1_tarski @ X21))),
% 0.40/0.57      inference('demod', [status(thm)], ['18', '23'])).
% 0.40/0.57  thf('27', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.40/0.57      inference('clc', [status(thm)], ['25', '26'])).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.40/0.57           = (k1_tarski @ (k4_tarski @ X2 @ X1)))),
% 0.40/0.57      inference('sup+', [status(thm)], ['1', '27'])).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.40/0.57      inference('clc', [status(thm)], ['25', '26'])).
% 0.40/0.57  thf('30', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['0', '28', '29'])).
% 0.40/0.57  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
