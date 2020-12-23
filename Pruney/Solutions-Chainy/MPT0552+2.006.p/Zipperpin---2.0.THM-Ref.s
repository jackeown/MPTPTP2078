%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qx0TZIM6e1

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:24 EST 2020

% Result     : Theorem 3.29s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  494 ( 844 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t104_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k7_relat_1 @ X20 @ X18 ) @ ( k7_relat_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t104_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k7_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qx0TZIM6e1
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:53:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 3.29/3.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.29/3.51  % Solved by: fo/fo7.sh
% 3.29/3.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.29/3.51  % done 6005 iterations in 3.045s
% 3.29/3.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.29/3.51  % SZS output start Refutation
% 3.29/3.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.29/3.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.29/3.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.29/3.51  thf(sk_B_type, type, sk_B: $i).
% 3.29/3.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.29/3.51  thf(sk_C_type, type, sk_C: $i).
% 3.29/3.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.29/3.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.29/3.51  thf(sk_A_type, type, sk_A: $i).
% 3.29/3.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.29/3.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.29/3.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.29/3.51  thf(commutativity_k2_tarski, axiom,
% 3.29/3.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.29/3.51  thf('0', plain,
% 3.29/3.51      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 3.29/3.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.29/3.51  thf(t148_relat_1, axiom,
% 3.29/3.51    (![A:$i,B:$i]:
% 3.29/3.51     ( ( v1_relat_1 @ B ) =>
% 3.29/3.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.29/3.51  thf('1', plain,
% 3.29/3.51      (![X21 : $i, X22 : $i]:
% 3.29/3.51         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 3.29/3.51          | ~ (v1_relat_1 @ X21))),
% 3.29/3.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.29/3.51  thf('2', plain,
% 3.29/3.51      (![X21 : $i, X22 : $i]:
% 3.29/3.51         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 3.29/3.51          | ~ (v1_relat_1 @ X21))),
% 3.29/3.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.29/3.51  thf(dt_k7_relat_1, axiom,
% 3.29/3.51    (![A:$i,B:$i]:
% 3.29/3.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 3.29/3.51  thf('3', plain,
% 3.29/3.51      (![X16 : $i, X17 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 3.29/3.51      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.29/3.51  thf(t17_xboole_1, axiom,
% 3.29/3.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.29/3.51  thf('4', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 3.29/3.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.29/3.51  thf(t12_setfam_1, axiom,
% 3.29/3.51    (![A:$i,B:$i]:
% 3.29/3.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.29/3.51  thf('5', plain,
% 3.29/3.51      (![X9 : $i, X10 : $i]:
% 3.29/3.51         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 3.29/3.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.29/3.51  thf('6', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i]:
% 3.29/3.51         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 3.29/3.51      inference('demod', [status(thm)], ['4', '5'])).
% 3.29/3.51  thf(t104_relat_1, axiom,
% 3.29/3.51    (![A:$i,B:$i,C:$i]:
% 3.29/3.51     ( ( v1_relat_1 @ C ) =>
% 3.29/3.51       ( ( r1_tarski @ A @ B ) =>
% 3.29/3.51         ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 3.29/3.51  thf('7', plain,
% 3.29/3.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.29/3.51         (~ (r1_tarski @ X18 @ X19)
% 3.29/3.51          | ~ (v1_relat_1 @ X20)
% 3.29/3.51          | (r1_tarski @ (k7_relat_1 @ X20 @ X18) @ (k7_relat_1 @ X20 @ X19)))),
% 3.29/3.51      inference('cnf', [status(esa)], [t104_relat_1])).
% 3.29/3.51  thf('8', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         ((r1_tarski @ 
% 3.29/3.51           (k7_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 3.29/3.51           (k7_relat_1 @ X2 @ X0))
% 3.29/3.51          | ~ (v1_relat_1 @ X2))),
% 3.29/3.51      inference('sup-', [status(thm)], ['6', '7'])).
% 3.29/3.51  thf(t25_relat_1, axiom,
% 3.29/3.51    (![A:$i]:
% 3.29/3.51     ( ( v1_relat_1 @ A ) =>
% 3.29/3.51       ( ![B:$i]:
% 3.29/3.51         ( ( v1_relat_1 @ B ) =>
% 3.29/3.51           ( ( r1_tarski @ A @ B ) =>
% 3.29/3.51             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 3.29/3.51               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 3.29/3.51  thf('9', plain,
% 3.29/3.51      (![X23 : $i, X24 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X23)
% 3.29/3.51          | (r1_tarski @ (k2_relat_1 @ X24) @ (k2_relat_1 @ X23))
% 3.29/3.51          | ~ (r1_tarski @ X24 @ X23)
% 3.29/3.51          | ~ (v1_relat_1 @ X24))),
% 3.29/3.51      inference('cnf', [status(esa)], [t25_relat_1])).
% 3.29/3.51  thf('10', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X1)
% 3.29/3.51          | ~ (v1_relat_1 @ 
% 3.29/3.51               (k7_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))))
% 3.29/3.51          | (r1_tarski @ 
% 3.29/3.51             (k2_relat_1 @ 
% 3.29/3.51              (k7_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2)))) @ 
% 3.29/3.51             (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 3.29/3.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.29/3.51      inference('sup-', [status(thm)], ['8', '9'])).
% 3.29/3.51  thf('11', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X2)
% 3.29/3.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 3.29/3.51          | (r1_tarski @ 
% 3.29/3.51             (k2_relat_1 @ 
% 3.29/3.51              (k7_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))) @ 
% 3.29/3.51             (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 3.29/3.51          | ~ (v1_relat_1 @ X2))),
% 3.29/3.51      inference('sup-', [status(thm)], ['3', '10'])).
% 3.29/3.51  thf('12', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         ((r1_tarski @ 
% 3.29/3.51           (k2_relat_1 @ 
% 3.29/3.51            (k7_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))) @ 
% 3.29/3.51           (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 3.29/3.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 3.29/3.51          | ~ (v1_relat_1 @ X2))),
% 3.29/3.51      inference('simplify', [status(thm)], ['11'])).
% 3.29/3.51  thf('13', plain,
% 3.29/3.51      (![X16 : $i, X17 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 3.29/3.51      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.29/3.51  thf('14', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X2)
% 3.29/3.51          | (r1_tarski @ 
% 3.29/3.51             (k2_relat_1 @ 
% 3.29/3.51              (k7_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))) @ 
% 3.29/3.51             (k2_relat_1 @ (k7_relat_1 @ X2 @ X1))))),
% 3.29/3.51      inference('clc', [status(thm)], ['12', '13'])).
% 3.29/3.51  thf('15', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         ((r1_tarski @ 
% 3.29/3.51           (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 3.29/3.51           (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 3.29/3.51          | ~ (v1_relat_1 @ X2)
% 3.29/3.51          | ~ (v1_relat_1 @ X2))),
% 3.29/3.51      inference('sup+', [status(thm)], ['2', '14'])).
% 3.29/3.51  thf('16', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X2)
% 3.29/3.51          | (r1_tarski @ 
% 3.29/3.51             (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 3.29/3.51             (k2_relat_1 @ (k7_relat_1 @ X2 @ X1))))),
% 3.29/3.51      inference('simplify', [status(thm)], ['15'])).
% 3.29/3.51  thf('17', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         ((r1_tarski @ 
% 3.29/3.51           (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 3.29/3.51           (k9_relat_1 @ X1 @ X0))
% 3.29/3.51          | ~ (v1_relat_1 @ X1)
% 3.29/3.51          | ~ (v1_relat_1 @ X1))),
% 3.29/3.51      inference('sup+', [status(thm)], ['1', '16'])).
% 3.29/3.51  thf('18', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X1)
% 3.29/3.51          | (r1_tarski @ 
% 3.29/3.51             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 3.29/3.51             (k9_relat_1 @ X1 @ X0)))),
% 3.29/3.51      inference('simplify', [status(thm)], ['17'])).
% 3.29/3.51  thf('19', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         ((r1_tarski @ 
% 3.29/3.51           (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 3.29/3.51           (k9_relat_1 @ X2 @ X0))
% 3.29/3.51          | ~ (v1_relat_1 @ X2))),
% 3.29/3.51      inference('sup+', [status(thm)], ['0', '18'])).
% 3.29/3.51  thf('20', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X1)
% 3.29/3.51          | (r1_tarski @ 
% 3.29/3.51             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 3.29/3.51             (k9_relat_1 @ X1 @ X0)))),
% 3.29/3.51      inference('simplify', [status(thm)], ['17'])).
% 3.29/3.51  thf(t19_xboole_1, axiom,
% 3.29/3.51    (![A:$i,B:$i,C:$i]:
% 3.29/3.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 3.29/3.51       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.29/3.51  thf('21', plain,
% 3.29/3.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.29/3.51         (~ (r1_tarski @ X2 @ X3)
% 3.29/3.51          | ~ (r1_tarski @ X2 @ X4)
% 3.29/3.51          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.29/3.51      inference('cnf', [status(esa)], [t19_xboole_1])).
% 3.29/3.51  thf('22', plain,
% 3.29/3.51      (![X9 : $i, X10 : $i]:
% 3.29/3.51         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 3.29/3.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.29/3.51  thf('23', plain,
% 3.29/3.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.29/3.51         (~ (r1_tarski @ X2 @ X3)
% 3.29/3.51          | ~ (r1_tarski @ X2 @ X4)
% 3.29/3.51          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 3.29/3.51      inference('demod', [status(thm)], ['21', '22'])).
% 3.29/3.51  thf('24', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X1)
% 3.29/3.51          | (r1_tarski @ 
% 3.29/3.51             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 3.29/3.51             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X3)))
% 3.29/3.51          | ~ (r1_tarski @ 
% 3.29/3.51               (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 3.29/3.51      inference('sup-', [status(thm)], ['20', '23'])).
% 3.29/3.51  thf('25', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         (~ (v1_relat_1 @ X1)
% 3.29/3.51          | (r1_tarski @ 
% 3.29/3.51             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 3.29/3.51             (k1_setfam_1 @ 
% 3.29/3.51              (k2_tarski @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))
% 3.29/3.51          | ~ (v1_relat_1 @ X1))),
% 3.29/3.51      inference('sup-', [status(thm)], ['19', '24'])).
% 3.29/3.51  thf('26', plain,
% 3.29/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.29/3.51         ((r1_tarski @ 
% 3.29/3.51           (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 3.29/3.51           (k1_setfam_1 @ 
% 3.29/3.51            (k2_tarski @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))
% 3.29/3.51          | ~ (v1_relat_1 @ X1))),
% 3.29/3.51      inference('simplify', [status(thm)], ['25'])).
% 3.29/3.51  thf(t154_relat_1, conjecture,
% 3.29/3.51    (![A:$i,B:$i,C:$i]:
% 3.29/3.51     ( ( v1_relat_1 @ C ) =>
% 3.29/3.51       ( r1_tarski @
% 3.29/3.51         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 3.29/3.51         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 3.29/3.51  thf(zf_stmt_0, negated_conjecture,
% 3.29/3.51    (~( ![A:$i,B:$i,C:$i]:
% 3.29/3.51        ( ( v1_relat_1 @ C ) =>
% 3.29/3.51          ( r1_tarski @
% 3.29/3.51            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 3.29/3.51            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 3.29/3.51    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 3.29/3.51  thf('27', plain,
% 3.29/3.51      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 3.29/3.51          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 3.29/3.51           (k9_relat_1 @ sk_C @ sk_B)))),
% 3.29/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.51  thf('28', plain,
% 3.29/3.51      (![X9 : $i, X10 : $i]:
% 3.29/3.51         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 3.29/3.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.29/3.51  thf('29', plain,
% 3.29/3.51      (![X9 : $i, X10 : $i]:
% 3.29/3.51         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 3.29/3.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.29/3.51  thf('30', plain,
% 3.29/3.51      (~ (r1_tarski @ 
% 3.29/3.51          (k9_relat_1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 3.29/3.51          (k1_setfam_1 @ 
% 3.29/3.51           (k2_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))))),
% 3.29/3.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 3.29/3.51  thf('31', plain, (~ (v1_relat_1 @ sk_C)),
% 3.29/3.51      inference('sup-', [status(thm)], ['26', '30'])).
% 3.29/3.51  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 3.29/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.51  thf('33', plain, ($false), inference('demod', [status(thm)], ['31', '32'])).
% 3.29/3.51  
% 3.29/3.51  % SZS output end Refutation
% 3.29/3.51  
% 3.29/3.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
