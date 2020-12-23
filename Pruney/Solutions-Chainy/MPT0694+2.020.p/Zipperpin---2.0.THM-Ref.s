%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lMPR04FRY0

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:34 EST 2020

% Result     : Theorem 4.00s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   55 (  64 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  498 ( 601 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X21 )
        = ( k9_relat_1 @ X23 @ X21 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k3_xboole_0 @ X26 @ ( k10_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X29 @ ( k10_relat_1 @ X29 @ X30 ) ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k9_relat_1 @ X20 @ X18 ) @ ( k9_relat_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

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
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','23'])).

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

thf('25',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lMPR04FRY0
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:40:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.00/4.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.00/4.24  % Solved by: fo/fo7.sh
% 4.00/4.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.00/4.24  % done 2278 iterations in 3.778s
% 4.00/4.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.00/4.24  % SZS output start Refutation
% 4.00/4.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.00/4.24  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.00/4.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.00/4.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.00/4.24  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.00/4.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.00/4.24  thf(sk_B_type, type, sk_B: $i).
% 4.00/4.24  thf(sk_A_type, type, sk_A: $i).
% 4.00/4.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.00/4.24  thf(sk_C_type, type, sk_C: $i).
% 4.00/4.24  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.00/4.24  thf(commutativity_k3_xboole_0, axiom,
% 4.00/4.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.00/4.24  thf('0', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.00/4.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.00/4.24  thf(t48_xboole_1, axiom,
% 4.00/4.24    (![A:$i,B:$i]:
% 4.00/4.24     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.00/4.24  thf('1', plain,
% 4.00/4.24      (![X7 : $i, X8 : $i]:
% 4.00/4.24         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 4.00/4.24           = (k3_xboole_0 @ X7 @ X8))),
% 4.00/4.24      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.00/4.24  thf(t36_xboole_1, axiom,
% 4.00/4.24    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.00/4.24  thf('2', plain,
% 4.00/4.24      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 4.00/4.24      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.00/4.24  thf('3', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.00/4.24      inference('sup+', [status(thm)], ['1', '2'])).
% 4.00/4.24  thf(t162_relat_1, axiom,
% 4.00/4.24    (![A:$i]:
% 4.00/4.24     ( ( v1_relat_1 @ A ) =>
% 4.00/4.24       ( ![B:$i,C:$i]:
% 4.00/4.24         ( ( r1_tarski @ B @ C ) =>
% 4.00/4.24           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 4.00/4.24             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 4.00/4.24  thf('4', plain,
% 4.00/4.24      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.00/4.24         (~ (r1_tarski @ X21 @ X22)
% 4.00/4.24          | ((k9_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X21)
% 4.00/4.24              = (k9_relat_1 @ X23 @ X21))
% 4.00/4.24          | ~ (v1_relat_1 @ X23))),
% 4.00/4.24      inference('cnf', [status(esa)], [t162_relat_1])).
% 4.00/4.24  thf('5', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         (~ (v1_relat_1 @ X2)
% 4.00/4.24          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 4.00/4.24              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 4.00/4.24      inference('sup-', [status(thm)], ['3', '4'])).
% 4.00/4.24  thf(fc8_funct_1, axiom,
% 4.00/4.24    (![A:$i,B:$i]:
% 4.00/4.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.00/4.24       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 4.00/4.24         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 4.00/4.24  thf('6', plain,
% 4.00/4.24      (![X24 : $i, X25 : $i]:
% 4.00/4.24         (~ (v1_funct_1 @ X24)
% 4.00/4.24          | ~ (v1_relat_1 @ X24)
% 4.00/4.24          | (v1_funct_1 @ (k7_relat_1 @ X24 @ X25)))),
% 4.00/4.24      inference('cnf', [status(esa)], [fc8_funct_1])).
% 4.00/4.24  thf(dt_k7_relat_1, axiom,
% 4.00/4.24    (![A:$i,B:$i]:
% 4.00/4.24     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 4.00/4.24  thf('7', plain,
% 4.00/4.24      (![X16 : $i, X17 : $i]:
% 4.00/4.24         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 4.00/4.24      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 4.00/4.24  thf(t139_funct_1, axiom,
% 4.00/4.24    (![A:$i,B:$i,C:$i]:
% 4.00/4.24     ( ( v1_relat_1 @ C ) =>
% 4.00/4.24       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 4.00/4.24         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.00/4.24  thf('8', plain,
% 4.00/4.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.00/4.24         (((k10_relat_1 @ (k7_relat_1 @ X27 @ X26) @ X28)
% 4.00/4.24            = (k3_xboole_0 @ X26 @ (k10_relat_1 @ X27 @ X28)))
% 4.00/4.24          | ~ (v1_relat_1 @ X27))),
% 4.00/4.24      inference('cnf', [status(esa)], [t139_funct_1])).
% 4.00/4.24  thf(t145_funct_1, axiom,
% 4.00/4.24    (![A:$i,B:$i]:
% 4.00/4.24     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.00/4.24       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 4.00/4.24  thf('9', plain,
% 4.00/4.24      (![X29 : $i, X30 : $i]:
% 4.00/4.24         ((r1_tarski @ (k9_relat_1 @ X29 @ (k10_relat_1 @ X29 @ X30)) @ X30)
% 4.00/4.24          | ~ (v1_funct_1 @ X29)
% 4.00/4.24          | ~ (v1_relat_1 @ X29))),
% 4.00/4.24      inference('cnf', [status(esa)], [t145_funct_1])).
% 4.00/4.24  thf('10', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         ((r1_tarski @ 
% 4.00/4.24           (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 4.00/4.24            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 4.00/4.24           X0)
% 4.00/4.24          | ~ (v1_relat_1 @ X1)
% 4.00/4.24          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2))
% 4.00/4.24          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X2)))),
% 4.00/4.24      inference('sup+', [status(thm)], ['8', '9'])).
% 4.00/4.24  thf('11', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         (~ (v1_relat_1 @ X1)
% 4.00/4.24          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 4.00/4.24          | ~ (v1_relat_1 @ X1)
% 4.00/4.24          | (r1_tarski @ 
% 4.00/4.24             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 4.00/4.24              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 4.00/4.24             X2))),
% 4.00/4.24      inference('sup-', [status(thm)], ['7', '10'])).
% 4.00/4.24  thf('12', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         ((r1_tarski @ 
% 4.00/4.24           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 4.00/4.24            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 4.00/4.24           X2)
% 4.00/4.24          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 4.00/4.24          | ~ (v1_relat_1 @ X1))),
% 4.00/4.24      inference('simplify', [status(thm)], ['11'])).
% 4.00/4.24  thf('13', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         (~ (v1_relat_1 @ X1)
% 4.00/4.24          | ~ (v1_funct_1 @ X1)
% 4.00/4.24          | ~ (v1_relat_1 @ X1)
% 4.00/4.24          | (r1_tarski @ 
% 4.00/4.24             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 4.00/4.24              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 4.00/4.24             X2))),
% 4.00/4.24      inference('sup-', [status(thm)], ['6', '12'])).
% 4.00/4.24  thf('14', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         ((r1_tarski @ 
% 4.00/4.24           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 4.00/4.24            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 4.00/4.24           X2)
% 4.00/4.24          | ~ (v1_funct_1 @ X1)
% 4.00/4.24          | ~ (v1_relat_1 @ X1))),
% 4.00/4.24      inference('simplify', [status(thm)], ['13'])).
% 4.00/4.24  thf('15', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         ((r1_tarski @ 
% 4.00/4.24           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 4.00/4.24           X0)
% 4.00/4.24          | ~ (v1_relat_1 @ X1)
% 4.00/4.24          | ~ (v1_relat_1 @ X1)
% 4.00/4.24          | ~ (v1_funct_1 @ X1))),
% 4.00/4.24      inference('sup+', [status(thm)], ['5', '14'])).
% 4.00/4.24  thf('16', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         (~ (v1_funct_1 @ X1)
% 4.00/4.24          | ~ (v1_relat_1 @ X1)
% 4.00/4.24          | (r1_tarski @ 
% 4.00/4.24             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 4.00/4.24             X0))),
% 4.00/4.24      inference('simplify', [status(thm)], ['15'])).
% 4.00/4.24  thf('17', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.00/4.24      inference('sup+', [status(thm)], ['1', '2'])).
% 4.00/4.24  thf(t156_relat_1, axiom,
% 4.00/4.24    (![A:$i,B:$i,C:$i]:
% 4.00/4.24     ( ( v1_relat_1 @ C ) =>
% 4.00/4.24       ( ( r1_tarski @ A @ B ) =>
% 4.00/4.24         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 4.00/4.24  thf('18', plain,
% 4.00/4.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.00/4.24         (~ (r1_tarski @ X18 @ X19)
% 4.00/4.24          | ~ (v1_relat_1 @ X20)
% 4.00/4.24          | (r1_tarski @ (k9_relat_1 @ X20 @ X18) @ (k9_relat_1 @ X20 @ X19)))),
% 4.00/4.24      inference('cnf', [status(esa)], [t156_relat_1])).
% 4.00/4.24  thf('19', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 4.00/4.24           (k9_relat_1 @ X2 @ X0))
% 4.00/4.24          | ~ (v1_relat_1 @ X2))),
% 4.00/4.24      inference('sup-', [status(thm)], ['17', '18'])).
% 4.00/4.24  thf(t19_xboole_1, axiom,
% 4.00/4.24    (![A:$i,B:$i,C:$i]:
% 4.00/4.24     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 4.00/4.24       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 4.00/4.24  thf('20', plain,
% 4.00/4.24      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.24         (~ (r1_tarski @ X2 @ X3)
% 4.00/4.24          | ~ (r1_tarski @ X2 @ X4)
% 4.00/4.24          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.00/4.24      inference('cnf', [status(esa)], [t19_xboole_1])).
% 4.00/4.24  thf('21', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.24         (~ (v1_relat_1 @ X1)
% 4.00/4.24          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 4.00/4.24             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 4.00/4.24          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 4.00/4.24      inference('sup-', [status(thm)], ['19', '20'])).
% 4.00/4.24  thf('22', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         (~ (v1_relat_1 @ X1)
% 4.00/4.24          | ~ (v1_funct_1 @ X1)
% 4.00/4.24          | (r1_tarski @ 
% 4.00/4.24             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 4.00/4.24             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 4.00/4.24          | ~ (v1_relat_1 @ X1))),
% 4.00/4.24      inference('sup-', [status(thm)], ['16', '21'])).
% 4.00/4.24  thf('23', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         ((r1_tarski @ 
% 4.00/4.24           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 4.00/4.24           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 4.00/4.24          | ~ (v1_funct_1 @ X1)
% 4.00/4.24          | ~ (v1_relat_1 @ X1))),
% 4.00/4.24      inference('simplify', [status(thm)], ['22'])).
% 4.00/4.24  thf('24', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.24         ((r1_tarski @ 
% 4.00/4.24           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 4.00/4.24           (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 4.00/4.24          | ~ (v1_relat_1 @ X1)
% 4.00/4.24          | ~ (v1_funct_1 @ X1))),
% 4.00/4.24      inference('sup+', [status(thm)], ['0', '23'])).
% 4.00/4.24  thf(t149_funct_1, conjecture,
% 4.00/4.24    (![A:$i,B:$i,C:$i]:
% 4.00/4.24     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.00/4.24       ( r1_tarski @
% 4.00/4.24         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 4.00/4.24         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 4.00/4.24  thf(zf_stmt_0, negated_conjecture,
% 4.00/4.24    (~( ![A:$i,B:$i,C:$i]:
% 4.00/4.24        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.00/4.24          ( r1_tarski @
% 4.00/4.24            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 4.00/4.24            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 4.00/4.24    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 4.00/4.24  thf('25', plain,
% 4.00/4.24      (~ (r1_tarski @ 
% 4.00/4.24          (k9_relat_1 @ sk_C @ 
% 4.00/4.24           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 4.00/4.24          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 4.00/4.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.24  thf('26', plain,
% 4.00/4.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.00/4.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.00/4.24  thf('27', plain,
% 4.00/4.24      (~ (r1_tarski @ 
% 4.00/4.24          (k9_relat_1 @ sk_C @ 
% 4.00/4.24           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 4.00/4.24          (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 4.00/4.24      inference('demod', [status(thm)], ['25', '26'])).
% 4.00/4.24  thf('28', plain, ((~ (v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 4.00/4.24      inference('sup-', [status(thm)], ['24', '27'])).
% 4.00/4.24  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 4.00/4.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.24  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 4.00/4.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.24  thf('31', plain, ($false),
% 4.00/4.24      inference('demod', [status(thm)], ['28', '29', '30'])).
% 4.00/4.24  
% 4.00/4.24  % SZS output end Refutation
% 4.00/4.24  
% 4.00/4.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
