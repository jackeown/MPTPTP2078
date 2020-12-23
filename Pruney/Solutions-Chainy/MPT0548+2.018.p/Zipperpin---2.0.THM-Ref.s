%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vqyRRzjK8w

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 (  91 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 ( 514 expanded)
%              Number of equality atoms :   57 (  73 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('0',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k9_relat_1 @ X32 @ X33 )
        = ( k9_relat_1 @ X32 @ ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k9_relat_1 @ X32 @ X33 )
        = ( k9_relat_1 @ X32 @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X32 ) @ X33 ) ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = ( k9_relat_1 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = ( k9_relat_1 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','35'])).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X34: $i] :
      ( ( ( k9_relat_1 @ X34 @ ( k1_relat_1 @ X34 ) )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('39',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('42',plain,
    ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','42'])).

thf('44',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vqyRRzjK8w
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 47 iterations in 0.019s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.48  thf(t150_relat_1, conjecture,
% 0.22/0.48    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.22/0.48  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t60_relat_1, axiom,
% 0.22/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf(t145_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( k9_relat_1 @ B @ A ) =
% 0.22/0.48         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X32 : $i, X33 : $i]:
% 0.22/0.48         (((k9_relat_1 @ X32 @ X33)
% 0.22/0.48            = (k9_relat_1 @ X32 @ (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33)))
% 0.22/0.48          | ~ (v1_relat_1 @ X32))),
% 0.22/0.48      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.22/0.48  thf(t12_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X29 : $i, X30 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X32 : $i, X33 : $i]:
% 0.22/0.48         (((k9_relat_1 @ X32 @ X33)
% 0.22/0.48            = (k9_relat_1 @ X32 @ 
% 0.22/0.48               (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X32) @ X33))))
% 0.22/0.48          | ~ (v1_relat_1 @ X32))),
% 0.22/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k9_relat_1 @ k1_xboole_0 @ X0)
% 0.22/0.48            = (k9_relat_1 @ k1_xboole_0 @ 
% 0.22/0.48               (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))))
% 0.22/0.48          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['1', '4'])).
% 0.22/0.48  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.48  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.48  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.48  thf('7', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.48  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k9_relat_1 @ k1_xboole_0 @ X0)
% 0.22/0.48           = (k9_relat_1 @ k1_xboole_0 @ 
% 0.22/0.48              (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))))),
% 0.22/0.48      inference('demod', [status(thm)], ['5', '8'])).
% 0.22/0.48  thf(t70_enumset1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i]:
% 0.22/0.48         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.48  thf(t100_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X2 @ X3)
% 0.22/0.48           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X29 : $i, X30 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X2 @ X3)
% 0.22/0.48           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.22/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X1 @ X0)
% 0.22/0.48           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))))),
% 0.22/0.48      inference('sup+', [status(thm)], ['10', '13'])).
% 0.22/0.48  thf(t2_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X29 : $i, X30 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X4 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X4 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X2 @ X3)
% 0.22/0.48           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.22/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf(t5_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.48  thf('20', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.48  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf(t98_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ X7 @ X8)
% 0.22/0.48           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf(t4_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ X7 @ X8)
% 0.22/0.48           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.48  thf('27', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.48  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.48  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.48  thf('31', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['23', '30'])).
% 0.22/0.48  thf('32', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k1_enumset1 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 0.22/0.48           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['14', '31'])).
% 0.22/0.48  thf('33', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i]:
% 0.22/0.48         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.48  thf('35', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.48  thf('36', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k9_relat_1 @ k1_xboole_0 @ X0)
% 0.22/0.48           = (k9_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['9', '35'])).
% 0.22/0.48  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf(t146_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      (![X34 : $i]:
% 0.22/0.48         (((k9_relat_1 @ X34 @ (k1_relat_1 @ X34)) = (k2_relat_1 @ X34))
% 0.22/0.48          | ~ (v1_relat_1 @ X34))),
% 0.22/0.48      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.22/0.48  thf('39', plain,
% 0.22/0.48      ((((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.22/0.48        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.48  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('42', plain,
% 0.22/0.48      (((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.22/0.48  thf('43', plain,
% 0.22/0.48      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['36', '42'])).
% 0.22/0.48  thf('44', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '43'])).
% 0.22/0.48  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
