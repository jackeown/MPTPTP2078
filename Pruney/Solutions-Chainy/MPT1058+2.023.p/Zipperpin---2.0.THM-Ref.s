%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JcHEuXiw8

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:40 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  378 ( 585 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('27',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('29',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JcHEuXiw8
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 487 iterations in 0.190s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(t175_funct_2, conjecture,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.64       ( ![B:$i,C:$i]:
% 0.47/0.64         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.47/0.64           ( ( k10_relat_1 @ A @ C ) =
% 0.47/0.64             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i]:
% 0.47/0.64        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.64          ( ![B:$i,C:$i]:
% 0.47/0.64            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.47/0.64              ( ( k10_relat_1 @ A @ C ) =
% 0.47/0.64                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.47/0.64  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t3_boole, axiom,
% 0.47/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.64  thf('1', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.64  thf(t36_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.47/0.64      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.64  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.64  thf(t19_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.47/0.64       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (r1_tarski @ X0 @ X2)
% 0.47/0.64          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.47/0.64        (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.64  thf(commutativity_k2_tarski, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X13 : $i, X14 : $i]:
% 0.47/0.64         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.47/0.64  thf(t12_setfam_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X20 : $i, X21 : $i]:
% 0.47/0.64         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.47/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['7', '8'])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X20 : $i, X21 : $i]:
% 0.47/0.64         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.47/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.47/0.64        (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.47/0.64      inference('demod', [status(thm)], ['6', '11'])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.47/0.64      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.64  thf(t1_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.64       ( r1_tarski @ A @ C ) ))).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.64         (~ (r1_tarski @ X3 @ X4)
% 0.47/0.64          | ~ (r1_tarski @ X4 @ X5)
% 0.47/0.64          | (r1_tarski @ X3 @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (r1_tarski @ (k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ X0) @ 
% 0.47/0.64          (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['12', '15'])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf(t48_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.47/0.64           = (k3_xboole_0 @ X11 @ X12))),
% 0.47/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.64  thf(t38_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.47/0.64       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X8 : $i, X9 : $i]:
% 0.47/0.64         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.64          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.64          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['17', '20'])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['16', '21'])).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.47/0.64           = (k3_xboole_0 @ X11 @ X12))),
% 0.47/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      (((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ k1_xboole_0)
% 0.47/0.64         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.47/0.64      inference('sup+', [status(thm)], ['22', '23'])).
% 0.47/0.64  thf('25', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      (((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.64         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.47/0.64      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.64  thf(t139_funct_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ C ) =>
% 0.47/0.64       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.47/0.64         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.47/0.64  thf('28', plain,
% 0.47/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.64         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 0.47/0.64            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 0.47/0.64          | ~ (v1_relat_1 @ X23))),
% 0.47/0.64      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.64         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.64          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.47/0.64        | ~ (v1_relat_1 @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.64  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      (((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.64         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.47/0.64      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.64  thf('33', plain, ($false),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['27', '32'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
