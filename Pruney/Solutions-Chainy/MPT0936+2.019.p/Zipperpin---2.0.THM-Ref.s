%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yesPddsLL3

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:25 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 117 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  338 ( 845 expanded)
%              Number of equality atoms :   48 ( 127 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k3_mcart_1 @ X43 @ X44 @ X45 )
      = ( k4_tarski @ ( k4_tarski @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_tarski @ ( k4_tarski @ X34 @ X35 ) @ ( k4_tarski @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) )
        = X41 )
      | ( X42 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( X32 != X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X31 ) )
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X31: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) )
     != ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X38: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X38 ) )
      = X38 ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
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

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X31: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X31 ) ) ),
    inference(demod,[status(thm)],['10','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(clc,[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X31: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X31 ) ) ),
    inference(demod,[status(thm)],['10','17','18'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('25',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','23','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yesPddsLL3
% 0.16/0.37  % Computer   : n015.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:47:53 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.22/0.38  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 190 iterations in 0.068s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.55  thf(t97_mcart_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( k1_relat_1 @
% 0.37/0.55         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.37/0.55       ( k1_tarski @ A ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ( k1_relat_1 @
% 0.37/0.55            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.37/0.55          ( k1_tarski @ A ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (((k1_relat_1 @ 
% 0.37/0.55         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))))
% 0.37/0.55         != (k1_tarski @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d3_mcart_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.55         ((k3_mcart_1 @ X43 @ X44 @ X45)
% 0.37/0.55           = (k4_tarski @ (k4_tarski @ X43 @ X44) @ X45))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.37/0.55  thf(t69_enumset1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.55  thf('2', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf(t36_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.37/0.55         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.37/0.55       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.37/0.55         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k1_tarski @ X34) @ (k2_tarski @ X35 @ X36))
% 0.37/0.55           = (k2_tarski @ (k4_tarski @ X34 @ X35) @ (k4_tarski @ X34 @ X36)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.37/0.55  thf('4', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.37/0.55           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.37/0.55           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['2', '5'])).
% 0.37/0.55  thf(t195_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.37/0.55               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X41 : $i, X42 : $i]:
% 0.37/0.55         (((X41) = (k1_xboole_0))
% 0.37/0.55          | ((k1_relat_1 @ (k2_zfmisc_1 @ X41 @ X42)) = (X41))
% 0.37/0.55          | ((X42) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.37/0.55            = (k1_tarski @ X1))
% 0.37/0.55          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.55          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf(t20_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.55         ( k1_tarski @ A ) ) <=>
% 0.37/0.55       ( ( A ) != ( B ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X31 : $i, X32 : $i]:
% 0.37/0.55         (((X32) != (X31))
% 0.37/0.55          | ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X31))
% 0.37/0.55              != (k1_tarski @ X32)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X31 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))
% 0.37/0.55           != (k1_tarski @ X31))),
% 0.37/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.55  thf('11', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf(t11_setfam_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.37/0.55  thf('12', plain, (![X38 : $i]: ((k1_setfam_1 @ (k1_tarski @ X38)) = (X38))),
% 0.37/0.55      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf(t12_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X39 : $i, X40 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf(t100_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf(t92_xboole_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('18', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('19', plain, (![X31 : $i]: ((k1_xboole_0) != (k1_tarski @ X31))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '17', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k1_tarski @ X1) = (k1_xboole_0))
% 0.37/0.55          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.37/0.55              = (k1_tarski @ X1)))),
% 0.37/0.55      inference('clc', [status(thm)], ['8', '19'])).
% 0.37/0.55  thf('21', plain, (![X31 : $i]: ((k1_xboole_0) != (k1_tarski @ X31))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '17', '18'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.37/0.55      inference('clc', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.37/0.55           = (k1_tarski @ (k4_tarski @ X2 @ X1)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['1', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.37/0.55      inference('clc', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf('25', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['0', '23', '24'])).
% 0.37/0.55  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
