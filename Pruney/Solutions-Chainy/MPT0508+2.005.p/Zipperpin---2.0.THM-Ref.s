%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T1NJkJxa5H

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  422 ( 621 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t106_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X15 @ X13 ) @ X14 )
        = ( k7_relat_1 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X19 @ X20 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t105_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k7_relat_1 @ X17 @ X18 ) @ ( k7_relat_1 @ X16 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t105_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X19 @ X20 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['7','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k7_relat_1 @ X17 @ X18 ) @ ( k7_relat_1 @ X16 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t105_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k7_relat_1 @ sk_C @ X0 ) @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_C @ X0 ) @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T1NJkJxa5H
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 79 iterations in 0.083s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(t106_relat_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ C ) =>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( v1_relat_1 @ D ) =>
% 0.21/0.54           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.21/0.54             ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ( v1_relat_1 @ C ) =>
% 0.21/0.54          ( ![D:$i]:
% 0.21/0.54            ( ( v1_relat_1 @ D ) =>
% 0.21/0.54              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.21/0.54                ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t106_relat_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (~ (r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t102_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ C ) =>
% 0.21/0.54       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.54         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.54          | ~ (v1_relat_1 @ X15)
% 0.21/0.54          | ((k7_relat_1 @ (k7_relat_1 @ X15 @ X13) @ X14)
% 0.21/0.54              = (k7_relat_1 @ X15 @ X13)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B)
% 0.21/0.54            = (k7_relat_1 @ X0 @ sk_A))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(t88_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         ((r1_tarski @ (k7_relat_1 @ X19 @ X20) @ X19) | ~ (v1_relat_1 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.21/0.54  thf(t105_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( v1_relat_1 @ C ) =>
% 0.21/0.54           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.54             ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X16)
% 0.21/0.54          | (r1_tarski @ (k7_relat_1 @ X17 @ X18) @ (k7_relat_1 @ X16 @ X18))
% 0.21/0.54          | ~ (r1_tarski @ X17 @ X16)
% 0.21/0.54          | ~ (v1_relat_1 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.21/0.54          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.21/0.54             (k7_relat_1 @ X0 @ X2))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.21/0.54           (k7_relat_1 @ X0 @ X2))
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         ((r1_tarski @ (k7_relat_1 @ X19 @ X20) @ X19) | ~ (v1_relat_1 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.21/0.54  thf(t28_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k3_xboole_0 @ (k7_relat_1 @ X0 @ X1) @ X0)
% 0.21/0.54              = (k7_relat_1 @ X0 @ X1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf(commutativity_k2_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.54  thf(t12_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k3_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.21/0.54              = (k7_relat_1 @ X0 @ X1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.54  thf(t48_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.21/0.54           = (k3_xboole_0 @ X5 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf(fc2_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['16', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.21/0.54             (k7_relat_1 @ X0 @ X2)))),
% 0.21/0.54      inference('clc', [status(thm)], ['7', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['3', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.54  thf('25', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X16)
% 0.21/0.54          | (r1_tarski @ (k7_relat_1 @ X17 @ X18) @ (k7_relat_1 @ X16 @ X18))
% 0.21/0.54          | ~ (r1_tarski @ X17 @ X16)
% 0.21/0.54          | ~ (v1_relat_1 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ sk_C)
% 0.21/0.54          | (r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ (k7_relat_1 @ sk_D @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.54  thf(t1_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.54       ( r1_tarski @ A @ C ) ))).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.54          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.54          | (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ X1)
% 0.21/0.54          | ~ (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.54        | (r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '32'])).
% 0.21/0.54  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
