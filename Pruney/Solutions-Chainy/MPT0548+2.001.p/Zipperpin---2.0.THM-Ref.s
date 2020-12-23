%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aYoIucTvsw

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 (  85 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  382 ( 473 expanded)
%              Number of equality atoms :   53 (  66 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k9_relat_1 @ X32 @ X33 )
        = ( k9_relat_1 @ X32 @ ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k9_relat_1 @ X32 @ X33 )
        = ( k9_relat_1 @ X32 @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X32 ) @ X33 ) ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = ( k9_relat_1 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('31',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X34: $i] :
      ( ( ( k9_relat_1 @ X34 @ ( k1_relat_1 @ X34 ) )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('33',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,
    ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','29','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aYoIucTvsw
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 53 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(t150_relat_1, conjecture,
% 0.21/0.47    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.21/0.47  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(cc1_relat_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.47  thf('1', plain, (![X31 : $i]: ((v1_relat_1 @ X31) | ~ (v1_xboole_0 @ X31))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.47  thf(t60_relat_1, axiom,
% 0.21/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('2', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf(t145_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( k9_relat_1 @ B @ A ) =
% 0.21/0.47         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X32 : $i, X33 : $i]:
% 0.21/0.47         (((k9_relat_1 @ X32 @ X33)
% 0.21/0.47            = (k9_relat_1 @ X32 @ (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33)))
% 0.21/0.47          | ~ (v1_relat_1 @ X32))),
% 0.21/0.47      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.21/0.47  thf(t12_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X29 : $i, X30 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X32 : $i, X33 : $i]:
% 0.21/0.47         (((k9_relat_1 @ X32 @ X33)
% 0.21/0.47            = (k9_relat_1 @ X32 @ 
% 0.21/0.47               (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X32) @ X33))))
% 0.21/0.47          | ~ (v1_relat_1 @ X32))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k9_relat_1 @ k1_xboole_0 @ X0)
% 0.21/0.47            = (k9_relat_1 @ k1_xboole_0 @ 
% 0.21/0.47               (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))))
% 0.21/0.47          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['2', '5'])).
% 0.21/0.47  thf(t100_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.47           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X29 : $i, X30 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.47           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(t2_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X29 : $i, X30 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X4 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ X4 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.47           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf(t5_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.47  thf('15', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.47  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf(t98_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ X7 @ X8)
% 0.21/0.47           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf(t4_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ X7 @ X8)
% 0.21/0.47           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.47  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.47  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['18', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))
% 0.21/0.47           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['9', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, (![X31 : $i]: ((v1_relat_1 @ X31) | ~ (v1_xboole_0 @ X31))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.47  thf('31', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf(t146_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X34 : $i]:
% 0.21/0.47         (((k9_relat_1 @ X34 @ (k1_relat_1 @ X34)) = (k2_relat_1 @ X34))
% 0.21/0.47          | ~ (v1_relat_1 @ X34))),
% 0.21/0.47      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      ((((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47        | ((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['30', '35'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '29', '38'])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47          | ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '39'])).
% 0.21/0.47  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.47  thf('43', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '42'])).
% 0.21/0.47  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
