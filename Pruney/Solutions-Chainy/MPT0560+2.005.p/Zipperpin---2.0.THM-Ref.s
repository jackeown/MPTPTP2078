%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WKdJxY86Ru

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  347 ( 462 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_C )
        = ( k7_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) @ X14 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ sk_B )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ sk_B )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ sk_B )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) @ X14 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WKdJxY86Ru
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 159 iterations in 0.135s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(t148_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ B ) =>
% 0.21/0.59       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      (![X18 : $i, X19 : $i]:
% 0.21/0.59         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.21/0.59          | ~ (v1_relat_1 @ X18))),
% 0.21/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.59  thf(t162_relat_1, conjecture,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ A ) =>
% 0.21/0.59       ( ![B:$i,C:$i]:
% 0.21/0.59         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.59           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.21/0.59             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i]:
% 0.21/0.59        ( ( v1_relat_1 @ A ) =>
% 0.21/0.59          ( ![B:$i,C:$i]:
% 0.21/0.59            ( ( r1_tarski @ B @ C ) =>
% 0.21/0.59              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.21/0.59                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 0.21/0.59  thf('1', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t102_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ C ) =>
% 0.21/0.59       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.59         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.59  thf('2', plain,
% 0.21/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X15 @ X16)
% 0.21/0.59          | ~ (v1_relat_1 @ X17)
% 0.21/0.59          | ((k7_relat_1 @ (k7_relat_1 @ X17 @ X15) @ X16)
% 0.21/0.59              = (k7_relat_1 @ X17 @ X15)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_C)
% 0.21/0.59            = (k7_relat_1 @ X0 @ sk_B))
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.59  thf(t100_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ C ) =>
% 0.21/0.59       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.59         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.21/0.59  thf('4', plain,
% 0.21/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         (((k7_relat_1 @ (k7_relat_1 @ X12 @ X13) @ X14)
% 0.21/0.59            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14)))
% 0.21/0.59          | ~ (v1_relat_1 @ X12))),
% 0.21/0.59      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k7_relat_1 @ X0 @ sk_B)
% 0.21/0.59            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.21/0.59          | ~ (v1_relat_1 @ X0)
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.59  thf(commutativity_k2_tarski, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.59  thf(t12_setfam_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (![X8 : $i, X9 : $i]:
% 0.21/0.59         ((k1_setfam_1 @ (k2_tarski @ X8 @ X9)) = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (![X8 : $i, X9 : $i]:
% 0.21/0.59         ((k1_setfam_1 @ (k2_tarski @ X8 @ X9)) = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.59      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k7_relat_1 @ X0 @ sk_B)
% 0.21/0.59            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ sk_C @ sk_B)))
% 0.21/0.59          | ~ (v1_relat_1 @ X0)
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0)
% 0.21/0.59          | ((k7_relat_1 @ X0 @ sk_B)
% 0.21/0.59              = (k7_relat_1 @ X0 @ (k3_xboole_0 @ sk_C @ sk_B))))),
% 0.21/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         (((k7_relat_1 @ (k7_relat_1 @ X12 @ X13) @ X14)
% 0.21/0.59            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14)))
% 0.21/0.59          | ~ (v1_relat_1 @ X12))),
% 0.21/0.59      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.21/0.59  thf('14', plain,
% 0.21/0.59      (![X18 : $i, X19 : $i]:
% 0.21/0.59         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.21/0.59          | ~ (v1_relat_1 @ X18))),
% 0.21/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.59            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ X2)
% 0.21/0.59          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.59  thf(dt_k7_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.59  thf('16', plain,
% 0.21/0.59      (![X10 : $i, X11 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.21/0.59      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.59  thf('17', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X2)
% 0.21/0.59          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.59              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.21/0.59      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.59  thf('18', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k2_relat_1 @ (k7_relat_1 @ X0 @ sk_B))
% 0.21/0.59            = (k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B))
% 0.21/0.59          | ~ (v1_relat_1 @ X0)
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['12', '17'])).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0)
% 0.21/0.59          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ sk_B))
% 0.21/0.59              = (k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.59         != (k9_relat_1 @ sk_A @ sk_B))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      ((((k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_B))
% 0.21/0.59          != (k9_relat_1 @ sk_A @ sk_B))
% 0.21/0.59        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.59  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (((k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_B)) != (k9_relat_1 @ sk_A @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      ((((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))
% 0.21/0.59        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['0', '23'])).
% 0.21/0.59  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('26', plain,
% 0.21/0.59      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.59  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
