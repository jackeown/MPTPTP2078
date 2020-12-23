%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RoB3ju2ffa

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:17 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   67 (  73 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  386 ( 448 expanded)
%              Number of equality atoms :   27 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X21 )
      | ( ( k4_xboole_0 @ X19 @ X21 )
       != X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t178_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_relat_1])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( r1_xboole_0 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['17','22'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['23','28'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X31 @ X32 ) @ ( k10_relat_1 @ X31 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RoB3ju2ffa
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 1161 iterations in 0.443s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.68/0.86  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.68/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.86  thf(t36_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.68/0.86  thf('0', plain,
% 0.68/0.86      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.68/0.86      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.86  thf(idempotence_k2_xboole_0, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.68/0.86  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.68/0.86      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.68/0.86  thf(t41_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.68/0.86       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.68/0.86           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.86  thf('3', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.68/0.86           = (k4_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['1', '2'])).
% 0.68/0.86  thf(t83_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      (![X19 : $i, X21 : $i]:
% 0.68/0.86         ((r1_xboole_0 @ X19 @ X21) | ((k4_xboole_0 @ X19 @ X21) != (X19)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.68/0.86  thf('5', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 0.68/0.86          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['3', '4'])).
% 0.68/0.86  thf('6', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.68/0.86      inference('simplify', [status(thm)], ['5'])).
% 0.68/0.86  thf(symmetry_r1_xboole_0, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      (![X2 : $i, X3 : $i]:
% 0.68/0.86         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.68/0.86      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.68/0.86  thf('8', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.68/0.86  thf(t178_relat_1, conjecture,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( v1_relat_1 @ C ) =>
% 0.68/0.86       ( ( r1_tarski @ A @ B ) =>
% 0.68/0.86         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.86        ( ( v1_relat_1 @ C ) =>
% 0.68/0.86          ( ( r1_tarski @ A @ B ) =>
% 0.68/0.86            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.68/0.86  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t63_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.68/0.86       ( r1_xboole_0 @ A @ C ) ))).
% 0.68/0.86  thf('10', plain,
% 0.68/0.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X12 @ X13)
% 0.68/0.86          | ~ (r1_xboole_0 @ X13 @ X14)
% 0.68/0.86          | (r1_xboole_0 @ X12 @ X14))),
% 0.68/0.86      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.86  thf('12', plain,
% 0.68/0.86      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.68/0.86      inference('sup-', [status(thm)], ['8', '11'])).
% 0.68/0.86  thf('13', plain,
% 0.68/0.86      (![X2 : $i, X3 : $i]:
% 0.68/0.86         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.68/0.86      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.68/0.86  thf('14', plain,
% 0.68/0.86      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.68/0.86      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.86  thf(t69_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.68/0.86       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.68/0.86  thf('15', plain,
% 0.68/0.86      (![X15 : $i, X16 : $i]:
% 0.68/0.86         (~ (r1_xboole_0 @ X15 @ X16)
% 0.68/0.86          | ~ (r1_tarski @ X15 @ X16)
% 0.68/0.86          | (v1_xboole_0 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.68/0.86  thf('16', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B))
% 0.68/0.86          | ~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.86  thf('17', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.86      inference('sup-', [status(thm)], ['0', '16'])).
% 0.68/0.86  thf(t39_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.86  thf('18', plain,
% 0.68/0.86      (![X7 : $i, X8 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.68/0.86           = (k2_xboole_0 @ X7 @ X8))),
% 0.68/0.86      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.68/0.86  thf(l13_xboole_0, axiom,
% 0.68/0.86    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.68/0.86  thf('19', plain,
% 0.68/0.86      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.86      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.86  thf(t1_boole, axiom,
% 0.68/0.86    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.86  thf('20', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.68/0.86      inference('cnf', [status(esa)], [t1_boole])).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (((k2_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['19', '20'])).
% 0.68/0.86  thf('22', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (((k2_xboole_0 @ X1 @ X0) = (X1))
% 0.68/0.86          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['18', '21'])).
% 0.68/0.86  thf('23', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.68/0.86      inference('sup-', [status(thm)], ['17', '22'])).
% 0.68/0.86  thf(commutativity_k2_tarski, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.68/0.86  thf('24', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i]:
% 0.68/0.86         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 0.68/0.86      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.68/0.86  thf(l51_zfmisc_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.86  thf('25', plain,
% 0.68/0.86      (![X29 : $i, X30 : $i]:
% 0.68/0.86         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 0.68/0.86      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.86  thf('26', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['24', '25'])).
% 0.68/0.86  thf('27', plain,
% 0.68/0.86      (![X29 : $i, X30 : $i]:
% 0.68/0.86         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 0.68/0.86      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.86  thf('28', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['26', '27'])).
% 0.68/0.86  thf('29', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.68/0.86      inference('demod', [status(thm)], ['23', '28'])).
% 0.68/0.86  thf(t175_relat_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( v1_relat_1 @ C ) =>
% 0.68/0.86       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.68/0.86         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.86  thf('30', plain,
% 0.68/0.86      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.68/0.86         (((k10_relat_1 @ X31 @ (k2_xboole_0 @ X32 @ X33))
% 0.68/0.86            = (k2_xboole_0 @ (k10_relat_1 @ X31 @ X32) @ 
% 0.68/0.86               (k10_relat_1 @ X31 @ X33)))
% 0.68/0.86          | ~ (v1_relat_1 @ X31))),
% 0.68/0.86      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.68/0.86  thf(t7_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.86  thf('31', plain,
% 0.68/0.86      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.68/0.86      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.86  thf('32', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.68/0.86           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.68/0.86          | ~ (v1_relat_1 @ X2))),
% 0.68/0.86      inference('sup+', [status(thm)], ['30', '31'])).
% 0.68/0.86  thf('33', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.68/0.86          | ~ (v1_relat_1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['29', '32'])).
% 0.68/0.86  thf('34', plain,
% 0.68/0.86      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('35', plain, (~ (v1_relat_1 @ sk_C)),
% 0.68/0.86      inference('sup-', [status(thm)], ['33', '34'])).
% 0.68/0.86  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('37', plain, ($false), inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.86  
% 0.68/0.86  % SZS output end Refutation
% 0.68/0.86  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
