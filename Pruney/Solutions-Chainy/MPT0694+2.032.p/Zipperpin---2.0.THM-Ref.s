%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lvnt5SeLXc

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  424 ( 497 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X12 @ X11 ) @ X10 )
        = ( k9_relat_1 @ X12 @ X10 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k9_relat_1 @ X9 @ X7 ) @ ( k9_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t149_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t149_funct_1])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lvnt5SeLXc
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:47:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 70 iterations in 0.105s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(t17_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.55  thf(t162_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i,C:$i]:
% 0.20/0.55         ( ( r1_tarski @ B @ C ) =>
% 0.20/0.55           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.20/0.55             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X10 @ X11)
% 0.20/0.55          | ((k9_relat_1 @ (k7_relat_1 @ X12 @ X11) @ X10)
% 0.20/0.55              = (k9_relat_1 @ X12 @ X10))
% 0.20/0.55          | ~ (v1_relat_1 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X2)
% 0.20/0.55          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.55              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(fc8_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.55       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.20/0.55         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X13)
% 0.20/0.55          | ~ (v1_relat_1 @ X13)
% 0.20/0.55          | (v1_funct_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.20/0.55  thf(dt_k7_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.55  thf(t139_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ C ) =>
% 0.20/0.55       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.55         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         (((k10_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X17)
% 0.20/0.55            = (k3_xboole_0 @ X15 @ (k10_relat_1 @ X16 @ X17)))
% 0.20/0.55          | ~ (v1_relat_1 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.20/0.55  thf(t145_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.55       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         ((r1_tarski @ (k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X19)) @ X19)
% 0.20/0.55          | ~ (v1_funct_1 @ X18)
% 0.20/0.55          | ~ (v1_relat_1 @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_tarski @ 
% 0.20/0.55           (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 0.20/0.55            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.55           X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2))
% 0.20/0.55          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | (r1_tarski @ 
% 0.20/0.55             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.55              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 0.20/0.55             X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_tarski @ 
% 0.20/0.55           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.55            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 0.20/0.55           X2)
% 0.20/0.55          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_funct_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | (r1_tarski @ 
% 0.20/0.55             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.55              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 0.20/0.55             X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_tarski @ 
% 0.20/0.55           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.55            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 0.20/0.55           X2)
% 0.20/0.55          | ~ (v1_funct_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_tarski @ 
% 0.20/0.55           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.55           X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_funct_1 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['2', '11'])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | (r1_tarski @ 
% 0.20/0.55             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.55             X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.55  thf(t156_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ C ) =>
% 0.20/0.55       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.55         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X7 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X9)
% 0.20/0.55          | (r1_tarski @ (k9_relat_1 @ X9 @ X7) @ (k9_relat_1 @ X9 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.20/0.55           (k9_relat_1 @ X2 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf(t19_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.20/0.55       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X2 @ X3)
% 0.20/0.55          | ~ (r1_tarski @ X2 @ X4)
% 0.20/0.55          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1)
% 0.20/0.55          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 0.20/0.55             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 0.20/0.55          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_funct_1 @ X1)
% 0.20/0.55          | (r1_tarski @ 
% 0.20/0.55             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.55             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_tarski @ 
% 0.20/0.55           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.55           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.55  thf(t149_funct_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55       ( r1_tarski @
% 0.20/0.55         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 0.20/0.55         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55          ( r1_tarski @
% 0.20/0.55            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 0.20/0.55            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (~ (r1_tarski @ 
% 0.20/0.55          (k9_relat_1 @ sk_C @ 
% 0.20/0.55           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 0.20/0.55          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('22', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('25', plain, ($false),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
