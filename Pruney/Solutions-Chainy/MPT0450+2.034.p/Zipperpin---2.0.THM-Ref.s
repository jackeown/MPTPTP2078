%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PFOc7MsGBc

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:06 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   56 (  75 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  424 ( 592 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X10 ) ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( r1_tarski @ ( k3_relat_1 @ X36 ) @ ( k3_relat_1 @ X35 ) )
      | ~ ( r1_tarski @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('17',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( r1_tarski @ ( k3_relat_1 @ X36 ) @ ( k3_relat_1 @ X35 ) )
      | ~ ( r1_tarski @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('24',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PFOc7MsGBc
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:09:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 339 iterations in 0.247s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.71  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.54/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.54/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(fc1_relat_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      (![X33 : $i, X34 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X33) | (v1_relat_1 @ (k3_xboole_0 @ X33 @ X34)))),
% 0.54/0.71      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.54/0.71  thf(t12_setfam_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i]:
% 0.54/0.71         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      (![X33 : $i, X34 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X33)
% 0.54/0.71          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X33 @ X34))))),
% 0.54/0.71      inference('demod', [status(thm)], ['0', '1'])).
% 0.54/0.71  thf(idempotence_k3_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.54/0.71  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.54/0.71  thf(t22_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.54/0.71  thf('4', plain,
% 0.54/0.71      (![X6 : $i, X7 : $i]:
% 0.54/0.71         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.54/0.71      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.54/0.71  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['3', '4'])).
% 0.54/0.71  thf(t31_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( r1_tarski @
% 0.54/0.71       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.54/0.71       ( k2_xboole_0 @ B @ C ) ))).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.71         (r1_tarski @ 
% 0.54/0.71          (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)) @ 
% 0.54/0.71          (k2_xboole_0 @ X9 @ X10))),
% 0.54/0.71      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i]:
% 0.54/0.71         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.71  thf('8', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i]:
% 0.54/0.71         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.71         (r1_tarski @ 
% 0.54/0.71          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ 
% 0.54/0.71           (k1_setfam_1 @ (k2_tarski @ X8 @ X10))) @ 
% 0.54/0.71          (k2_xboole_0 @ X9 @ X10))),
% 0.54/0.71      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.54/0.71          (k2_xboole_0 @ X0 @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['5', '9'])).
% 0.54/0.71  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['3', '4'])).
% 0.54/0.71  thf('12', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.54/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.71  thf(t31_relat_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( v1_relat_1 @ B ) =>
% 0.54/0.71           ( ( r1_tarski @ A @ B ) =>
% 0.54/0.71             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.54/0.71  thf('13', plain,
% 0.54/0.71      (![X35 : $i, X36 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X35)
% 0.54/0.71          | (r1_tarski @ (k3_relat_1 @ X36) @ (k3_relat_1 @ X35))
% 0.54/0.71          | ~ (r1_tarski @ X36 @ X35)
% 0.54/0.71          | ~ (v1_relat_1 @ X36))),
% 0.54/0.71      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.54/0.71          | (r1_tarski @ 
% 0.54/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.54/0.71             (k3_relat_1 @ X0))
% 0.54/0.71          | ~ (v1_relat_1 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X1)
% 0.54/0.71          | ~ (v1_relat_1 @ X0)
% 0.54/0.71          | (r1_tarski @ 
% 0.54/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.54/0.71             (k3_relat_1 @ X0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['2', '14'])).
% 0.54/0.71  thf(t17_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.54/0.71      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i]:
% 0.54/0.71         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.71  thf('18', plain,
% 0.54/0.71      (![X1 : $i, X2 : $i]:
% 0.54/0.71         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2)) @ X1)),
% 0.54/0.71      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      (![X35 : $i, X36 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X35)
% 0.54/0.71          | (r1_tarski @ (k3_relat_1 @ X36) @ (k3_relat_1 @ X35))
% 0.54/0.71          | ~ (r1_tarski @ X36 @ X35)
% 0.54/0.71          | ~ (v1_relat_1 @ X36))),
% 0.54/0.71      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.54/0.71  thf('20', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.54/0.71          | (r1_tarski @ 
% 0.54/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.54/0.71             (k3_relat_1 @ X0))
% 0.54/0.71          | ~ (v1_relat_1 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.71  thf('21', plain,
% 0.54/0.71      (![X33 : $i, X34 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X33)
% 0.54/0.71          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X33 @ X34))))),
% 0.54/0.71      inference('demod', [status(thm)], ['0', '1'])).
% 0.54/0.71  thf('22', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X0)
% 0.54/0.71          | (r1_tarski @ 
% 0.54/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.54/0.71             (k3_relat_1 @ X0)))),
% 0.54/0.71      inference('clc', [status(thm)], ['20', '21'])).
% 0.54/0.71  thf(t19_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.54/0.71       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.54/0.71  thf('23', plain,
% 0.54/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.71         (~ (r1_tarski @ X3 @ X4)
% 0.54/0.71          | ~ (r1_tarski @ X3 @ X5)
% 0.54/0.71          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i]:
% 0.54/0.71         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.71  thf('25', plain,
% 0.54/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.71         (~ (r1_tarski @ X3 @ X4)
% 0.54/0.71          | ~ (r1_tarski @ X3 @ X5)
% 0.54/0.71          | (r1_tarski @ X3 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 0.54/0.71      inference('demod', [status(thm)], ['23', '24'])).
% 0.54/0.71  thf('26', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X0)
% 0.54/0.71          | (r1_tarski @ 
% 0.54/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.54/0.71             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X0) @ X2)))
% 0.54/0.71          | ~ (r1_tarski @ 
% 0.54/0.71               (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.54/0.71      inference('sup-', [status(thm)], ['22', '25'])).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (~ (v1_relat_1 @ X0)
% 0.54/0.71          | ~ (v1_relat_1 @ X1)
% 0.54/0.71          | (r1_tarski @ 
% 0.54/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.54/0.71             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0))))
% 0.54/0.71          | ~ (v1_relat_1 @ X1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['15', '26'])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((r1_tarski @ (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.54/0.71           (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0))))
% 0.54/0.71          | ~ (v1_relat_1 @ X1)
% 0.54/0.71          | ~ (v1_relat_1 @ X0))),
% 0.54/0.71      inference('simplify', [status(thm)], ['27'])).
% 0.54/0.71  thf(t34_relat_1, conjecture,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( v1_relat_1 @ B ) =>
% 0.54/0.71           ( r1_tarski @
% 0.54/0.71             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.54/0.71             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i]:
% 0.54/0.71        ( ( v1_relat_1 @ A ) =>
% 0.54/0.71          ( ![B:$i]:
% 0.54/0.71            ( ( v1_relat_1 @ B ) =>
% 0.54/0.71              ( r1_tarski @
% 0.54/0.71                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.54/0.71                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.54/0.71          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('30', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i]:
% 0.54/0.71         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.71  thf('31', plain,
% 0.54/0.71      (![X31 : $i, X32 : $i]:
% 0.54/0.71         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      (~ (r1_tarski @ 
% 0.54/0.71          (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.54/0.71          (k1_setfam_1 @ 
% 0.54/0.71           (k2_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))))),
% 0.54/0.71      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.54/0.71  thf('33', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['28', '32'])).
% 0.54/0.71  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('36', plain, ($false),
% 0.54/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
