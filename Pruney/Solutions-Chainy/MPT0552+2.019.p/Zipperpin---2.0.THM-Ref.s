%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rMwVDYz1Br

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:26 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   53 (  78 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  422 ( 694 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k9_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k9_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t108_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X21 @ X22 ) @ ( k7_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t108_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rMwVDYz1Br
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.64/1.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.64/1.81  % Solved by: fo/fo7.sh
% 1.64/1.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.81  % done 1173 iterations in 1.338s
% 1.64/1.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.64/1.81  % SZS output start Refutation
% 1.64/1.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.64/1.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.64/1.81  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.64/1.81  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.81  thf(sk_C_type, type, sk_C: $i).
% 1.64/1.81  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.64/1.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.64/1.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.64/1.81  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.64/1.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.64/1.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.64/1.81  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.81  thf(commutativity_k2_tarski, axiom,
% 1.64/1.81    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.64/1.81  thf('0', plain,
% 1.64/1.81      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 1.64/1.81      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.64/1.81  thf(t12_setfam_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.64/1.81  thf('1', plain,
% 1.64/1.81      (![X15 : $i, X16 : $i]:
% 1.64/1.81         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 1.64/1.81      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.64/1.81  thf('2', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i]:
% 1.64/1.81         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.64/1.81      inference('sup+', [status(thm)], ['0', '1'])).
% 1.64/1.81  thf('3', plain,
% 1.64/1.81      (![X15 : $i, X16 : $i]:
% 1.64/1.81         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 1.64/1.81      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.64/1.81  thf('4', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.64/1.81      inference('sup+', [status(thm)], ['2', '3'])).
% 1.64/1.81  thf(t148_relat_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( v1_relat_1 @ B ) =>
% 1.64/1.81       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.64/1.81  thf('5', plain,
% 1.64/1.81      (![X24 : $i, X25 : $i]:
% 1.64/1.81         (((k2_relat_1 @ (k7_relat_1 @ X24 @ X25)) = (k9_relat_1 @ X24 @ X25))
% 1.64/1.81          | ~ (v1_relat_1 @ X24))),
% 1.64/1.81      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.64/1.81  thf('6', plain,
% 1.64/1.81      (![X24 : $i, X25 : $i]:
% 1.64/1.81         (((k2_relat_1 @ (k7_relat_1 @ X24 @ X25)) = (k9_relat_1 @ X24 @ X25))
% 1.64/1.81          | ~ (v1_relat_1 @ X24))),
% 1.64/1.81      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.64/1.81  thf(t108_relat_1, axiom,
% 1.64/1.81    (![A:$i,B:$i,C:$i]:
% 1.64/1.81     ( ( v1_relat_1 @ C ) =>
% 1.64/1.81       ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 1.64/1.81         ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 1.64/1.81  thf('7', plain,
% 1.64/1.81      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.64/1.81         (((k7_relat_1 @ X21 @ (k3_xboole_0 @ X22 @ X23))
% 1.64/1.81            = (k3_xboole_0 @ (k7_relat_1 @ X21 @ X22) @ 
% 1.64/1.81               (k7_relat_1 @ X21 @ X23)))
% 1.64/1.81          | ~ (v1_relat_1 @ X21))),
% 1.64/1.81      inference('cnf', [status(esa)], [t108_relat_1])).
% 1.64/1.81  thf(t17_xboole_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.64/1.81  thf('8', plain,
% 1.64/1.81      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.64/1.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.64/1.81  thf(t25_relat_1, axiom,
% 1.64/1.81    (![A:$i]:
% 1.64/1.81     ( ( v1_relat_1 @ A ) =>
% 1.64/1.81       ( ![B:$i]:
% 1.64/1.81         ( ( v1_relat_1 @ B ) =>
% 1.64/1.81           ( ( r1_tarski @ A @ B ) =>
% 1.64/1.81             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.64/1.81               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.64/1.81  thf('9', plain,
% 1.64/1.81      (![X26 : $i, X27 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X26)
% 1.64/1.81          | (r1_tarski @ (k2_relat_1 @ X27) @ (k2_relat_1 @ X26))
% 1.64/1.81          | ~ (r1_tarski @ X27 @ X26)
% 1.64/1.81          | ~ (v1_relat_1 @ X27))),
% 1.64/1.81      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.64/1.81  thf('10', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.64/1.81          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.64/1.81             (k2_relat_1 @ X0))
% 1.64/1.81          | ~ (v1_relat_1 @ X0))),
% 1.64/1.81      inference('sup-', [status(thm)], ['8', '9'])).
% 1.64/1.81  thf(fc1_relat_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.64/1.81  thf('11', plain,
% 1.64/1.81      (![X19 : $i, X20 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k3_xboole_0 @ X19 @ X20)))),
% 1.64/1.81      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.64/1.81  thf('12', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X0)
% 1.64/1.81          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.64/1.81             (k2_relat_1 @ X0)))),
% 1.64/1.81      inference('clc', [status(thm)], ['10', '11'])).
% 1.64/1.81  thf('13', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         ((r1_tarski @ 
% 1.64/1.81           (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 1.64/1.81           (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 1.64/1.81          | ~ (v1_relat_1 @ X2)
% 1.64/1.81          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 1.64/1.81      inference('sup+', [status(thm)], ['7', '12'])).
% 1.64/1.81  thf(dt_k7_relat_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.64/1.81  thf('14', plain,
% 1.64/1.81      (![X17 : $i, X18 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 1.64/1.81      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.64/1.81  thf('15', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X2)
% 1.64/1.81          | (r1_tarski @ 
% 1.64/1.81             (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 1.64/1.81             (k2_relat_1 @ (k7_relat_1 @ X2 @ X1))))),
% 1.64/1.81      inference('clc', [status(thm)], ['13', '14'])).
% 1.64/1.81  thf('16', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.64/1.81           (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 1.64/1.81          | ~ (v1_relat_1 @ X2)
% 1.64/1.81          | ~ (v1_relat_1 @ X2))),
% 1.64/1.81      inference('sup+', [status(thm)], ['6', '15'])).
% 1.64/1.81  thf('17', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X2)
% 1.64/1.81          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.64/1.81             (k2_relat_1 @ (k7_relat_1 @ X2 @ X1))))),
% 1.64/1.81      inference('simplify', [status(thm)], ['16'])).
% 1.64/1.81  thf('18', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.64/1.81           (k9_relat_1 @ X1 @ X0))
% 1.64/1.81          | ~ (v1_relat_1 @ X1)
% 1.64/1.81          | ~ (v1_relat_1 @ X1))),
% 1.64/1.81      inference('sup+', [status(thm)], ['5', '17'])).
% 1.64/1.81  thf('19', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X1)
% 1.64/1.81          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.64/1.81             (k9_relat_1 @ X1 @ X0)))),
% 1.64/1.81      inference('simplify', [status(thm)], ['18'])).
% 1.64/1.81  thf('20', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.64/1.81           (k9_relat_1 @ X2 @ X0))
% 1.64/1.81          | ~ (v1_relat_1 @ X2))),
% 1.64/1.81      inference('sup+', [status(thm)], ['4', '19'])).
% 1.64/1.81  thf('21', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X1)
% 1.64/1.81          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.64/1.81             (k9_relat_1 @ X1 @ X0)))),
% 1.64/1.81      inference('simplify', [status(thm)], ['18'])).
% 1.64/1.81  thf(t19_xboole_1, axiom,
% 1.64/1.81    (![A:$i,B:$i,C:$i]:
% 1.64/1.81     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.64/1.81       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.64/1.81  thf('22', plain,
% 1.64/1.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.64/1.81         (~ (r1_tarski @ X5 @ X6)
% 1.64/1.81          | ~ (r1_tarski @ X5 @ X7)
% 1.64/1.81          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.64/1.81      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.64/1.81  thf('23', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X1)
% 1.64/1.81          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.64/1.81             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 1.64/1.81          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 1.64/1.81      inference('sup-', [status(thm)], ['21', '22'])).
% 1.64/1.81  thf('24', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         (~ (v1_relat_1 @ X1)
% 1.64/1.81          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.64/1.81             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 1.64/1.81          | ~ (v1_relat_1 @ X1))),
% 1.64/1.81      inference('sup-', [status(thm)], ['20', '23'])).
% 1.64/1.81  thf('25', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.64/1.81           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 1.64/1.81          | ~ (v1_relat_1 @ X1))),
% 1.64/1.81      inference('simplify', [status(thm)], ['24'])).
% 1.64/1.81  thf(t154_relat_1, conjecture,
% 1.64/1.81    (![A:$i,B:$i,C:$i]:
% 1.64/1.81     ( ( v1_relat_1 @ C ) =>
% 1.64/1.81       ( r1_tarski @
% 1.64/1.81         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.64/1.81         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.64/1.81  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.81    (~( ![A:$i,B:$i,C:$i]:
% 1.64/1.81        ( ( v1_relat_1 @ C ) =>
% 1.64/1.81          ( r1_tarski @
% 1.64/1.81            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.64/1.81            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 1.64/1.81    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 1.64/1.81  thf('26', plain,
% 1.64/1.81      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 1.64/1.81          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 1.64/1.81           (k9_relat_1 @ sk_C @ sk_B)))),
% 1.64/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.81  thf('27', plain, (~ (v1_relat_1 @ sk_C)),
% 1.64/1.81      inference('sup-', [status(thm)], ['25', '26'])).
% 1.64/1.81  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 1.64/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.81  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 1.64/1.81  
% 1.64/1.81  % SZS output end Refutation
% 1.64/1.81  
% 1.64/1.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
