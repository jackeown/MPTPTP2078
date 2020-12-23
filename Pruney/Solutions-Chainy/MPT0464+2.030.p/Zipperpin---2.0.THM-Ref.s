%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BukAcyI1uc

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:12 EST 2020

% Result     : Theorem 33.73s
% Output     : Refutation 33.73s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  390 ( 593 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( r1_tarski @ ( k5_relat_1 @ X15 @ X14 ) @ ( k5_relat_1 @ X15 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( r1_tarski @ ( k5_relat_1 @ X15 @ X14 ) @ ( k5_relat_1 @ X15 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['25','26','27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BukAcyI1uc
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 33.73/33.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 33.73/33.94  % Solved by: fo/fo7.sh
% 33.73/33.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.73/33.94  % done 8622 iterations in 33.482s
% 33.73/33.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 33.73/33.94  % SZS output start Refutation
% 33.73/33.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 33.73/33.94  thf(sk_C_type, type, sk_C: $i).
% 33.73/33.94  thf(sk_A_type, type, sk_A: $i).
% 33.73/33.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 33.73/33.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 33.73/33.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 33.73/33.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 33.73/33.94  thf(sk_B_type, type, sk_B: $i).
% 33.73/33.94  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 33.73/33.94  thf(commutativity_k2_tarski, axiom,
% 33.73/33.94    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 33.73/33.94  thf('0', plain,
% 33.73/33.94      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 33.73/33.94      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 33.73/33.94  thf(t12_setfam_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 33.73/33.94  thf('1', plain,
% 33.73/33.94      (![X9 : $i, X10 : $i]:
% 33.73/33.94         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 33.73/33.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 33.73/33.94  thf('2', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup+', [status(thm)], ['0', '1'])).
% 33.73/33.94  thf('3', plain,
% 33.73/33.94      (![X9 : $i, X10 : $i]:
% 33.73/33.94         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 33.73/33.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 33.73/33.94  thf('4', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup+', [status(thm)], ['2', '3'])).
% 33.73/33.94  thf(fc1_relat_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]:
% 33.73/33.94     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 33.73/33.94  thf('5', plain,
% 33.73/33.94      (![X11 : $i, X12 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k3_xboole_0 @ X11 @ X12)))),
% 33.73/33.94      inference('cnf', [status(esa)], [fc1_relat_1])).
% 33.73/33.94  thf('6', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]:
% 33.73/33.94         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 33.73/33.94      inference('sup+', [status(thm)], ['4', '5'])).
% 33.73/33.94  thf('7', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 33.73/33.94      inference('sup+', [status(thm)], ['2', '3'])).
% 33.73/33.94  thf(t17_xboole_1, axiom,
% 33.73/33.94    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 33.73/33.94  thf('8', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 33.73/33.94      inference('cnf', [status(esa)], [t17_xboole_1])).
% 33.73/33.94  thf('9', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 33.73/33.94      inference('sup+', [status(thm)], ['7', '8'])).
% 33.73/33.94  thf(t48_relat_1, axiom,
% 33.73/33.94    (![A:$i]:
% 33.73/33.94     ( ( v1_relat_1 @ A ) =>
% 33.73/33.94       ( ![B:$i]:
% 33.73/33.94         ( ( v1_relat_1 @ B ) =>
% 33.73/33.94           ( ![C:$i]:
% 33.73/33.94             ( ( v1_relat_1 @ C ) =>
% 33.73/33.94               ( ( r1_tarski @ A @ B ) =>
% 33.73/33.94                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 33.73/33.94  thf('10', plain,
% 33.73/33.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X13)
% 33.73/33.94          | ~ (r1_tarski @ X14 @ X13)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X15 @ X14) @ (k5_relat_1 @ X15 @ X13))
% 33.73/33.94          | ~ (v1_relat_1 @ X15)
% 33.73/33.94          | ~ (v1_relat_1 @ X14))),
% 33.73/33.94      inference('cnf', [status(esa)], [t48_relat_1])).
% 33.73/33.94  thf('11', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 33.73/33.94          | ~ (v1_relat_1 @ X2)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 33.73/33.94             (k5_relat_1 @ X2 @ X0))
% 33.73/33.94          | ~ (v1_relat_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['9', '10'])).
% 33.73/33.94  thf('12', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X0)
% 33.73/33.94          | ~ (v1_relat_1 @ X0)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 33.73/33.94             (k5_relat_1 @ X2 @ X0))
% 33.73/33.94          | ~ (v1_relat_1 @ X2))),
% 33.73/33.94      inference('sup-', [status(thm)], ['6', '11'])).
% 33.73/33.94  thf('13', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X2)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 33.73/33.94             (k5_relat_1 @ X2 @ X0))
% 33.73/33.94          | ~ (v1_relat_1 @ X0))),
% 33.73/33.94      inference('simplify', [status(thm)], ['12'])).
% 33.73/33.94  thf('14', plain,
% 33.73/33.94      (![X11 : $i, X12 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k3_xboole_0 @ X11 @ X12)))),
% 33.73/33.94      inference('cnf', [status(esa)], [fc1_relat_1])).
% 33.73/33.94  thf('15', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 33.73/33.94      inference('cnf', [status(esa)], [t17_xboole_1])).
% 33.73/33.94  thf('16', plain,
% 33.73/33.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X13)
% 33.73/33.94          | ~ (r1_tarski @ X14 @ X13)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X15 @ X14) @ (k5_relat_1 @ X15 @ X13))
% 33.73/33.94          | ~ (v1_relat_1 @ X15)
% 33.73/33.94          | ~ (v1_relat_1 @ X14))),
% 33.73/33.94      inference('cnf', [status(esa)], [t48_relat_1])).
% 33.73/33.94  thf('17', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 33.73/33.94          | ~ (v1_relat_1 @ X2)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 33.73/33.94             (k5_relat_1 @ X2 @ X0))
% 33.73/33.94          | ~ (v1_relat_1 @ X0))),
% 33.73/33.94      inference('sup-', [status(thm)], ['15', '16'])).
% 33.73/33.94  thf('18', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X1)
% 33.73/33.94          | ~ (v1_relat_1 @ X1)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 33.73/33.94             (k5_relat_1 @ X2 @ X1))
% 33.73/33.94          | ~ (v1_relat_1 @ X2))),
% 33.73/33.94      inference('sup-', [status(thm)], ['14', '17'])).
% 33.73/33.94  thf('19', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X2)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 33.73/33.94             (k5_relat_1 @ X2 @ X1))
% 33.73/33.94          | ~ (v1_relat_1 @ X1))),
% 33.73/33.94      inference('simplify', [status(thm)], ['18'])).
% 33.73/33.94  thf(t19_xboole_1, axiom,
% 33.73/33.94    (![A:$i,B:$i,C:$i]:
% 33.73/33.94     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 33.73/33.94       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 33.73/33.94  thf('20', plain,
% 33.73/33.94      (![X2 : $i, X3 : $i, X4 : $i]:
% 33.73/33.94         (~ (r1_tarski @ X2 @ X3)
% 33.73/33.94          | ~ (r1_tarski @ X2 @ X4)
% 33.73/33.94          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 33.73/33.94      inference('cnf', [status(esa)], [t19_xboole_1])).
% 33.73/33.94  thf('21', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X0)
% 33.73/33.94          | ~ (v1_relat_1 @ X1)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 33.73/33.94             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 33.73/33.94          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 33.73/33.94      inference('sup-', [status(thm)], ['19', '20'])).
% 33.73/33.94  thf('22', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X0)
% 33.73/33.94          | ~ (v1_relat_1 @ X1)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 33.73/33.94             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 33.73/33.94          | ~ (v1_relat_1 @ X1)
% 33.73/33.94          | ~ (v1_relat_1 @ X2))),
% 33.73/33.94      inference('sup-', [status(thm)], ['13', '21'])).
% 33.73/33.94  thf('23', plain,
% 33.73/33.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.73/33.94         (~ (v1_relat_1 @ X2)
% 33.73/33.94          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 33.73/33.94             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 33.73/33.94          | ~ (v1_relat_1 @ X1)
% 33.73/33.94          | ~ (v1_relat_1 @ X0))),
% 33.73/33.94      inference('simplify', [status(thm)], ['22'])).
% 33.73/33.94  thf(t52_relat_1, conjecture,
% 33.73/33.94    (![A:$i]:
% 33.73/33.94     ( ( v1_relat_1 @ A ) =>
% 33.73/33.94       ( ![B:$i]:
% 33.73/33.94         ( ( v1_relat_1 @ B ) =>
% 33.73/33.94           ( ![C:$i]:
% 33.73/33.94             ( ( v1_relat_1 @ C ) =>
% 33.73/33.94               ( r1_tarski @
% 33.73/33.94                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 33.73/33.94                 ( k3_xboole_0 @
% 33.73/33.94                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 33.73/33.94  thf(zf_stmt_0, negated_conjecture,
% 33.73/33.94    (~( ![A:$i]:
% 33.73/33.94        ( ( v1_relat_1 @ A ) =>
% 33.73/33.94          ( ![B:$i]:
% 33.73/33.94            ( ( v1_relat_1 @ B ) =>
% 33.73/33.94              ( ![C:$i]:
% 33.73/33.94                ( ( v1_relat_1 @ C ) =>
% 33.73/33.94                  ( r1_tarski @
% 33.73/33.94                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 33.73/33.94                    ( k3_xboole_0 @
% 33.73/33.94                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 33.73/33.94    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 33.73/33.94  thf('24', plain,
% 33.73/33.94      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 33.73/33.94          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 33.73/33.94           (k5_relat_1 @ sk_A @ sk_C)))),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('25', plain,
% 33.73/33.94      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 33.73/33.94      inference('sup-', [status(thm)], ['23', '24'])).
% 33.73/33.94  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 33.73/33.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.73/33.94  thf('29', plain, ($false),
% 33.73/33.94      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 33.73/33.94  
% 33.73/33.94  % SZS output end Refutation
% 33.73/33.94  
% 33.73/33.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
