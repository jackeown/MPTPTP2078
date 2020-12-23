%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a5IRDH0kiP

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:04 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  401 ( 597 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t163_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t163_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( r1_tarski @ X18 @ ( k10_relat_1 @ X19 @ ( k9_relat_1 @ X19 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
        = ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23','24'])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a5IRDH0kiP
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 551 iterations in 0.338s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.61/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.81  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.61/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(t163_funct_1, conjecture,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.61/0.81       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.61/0.81           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.61/0.81         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.81        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.61/0.81          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.61/0.81              ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.61/0.81            ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t163_funct_1])).
% 0.61/0.81  thf('0', plain, (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('1', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t12_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.61/0.81  thf('2', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i]:
% 0.61/0.81         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.81  thf('3', plain,
% 0.61/0.81      (((k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B) = (sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.81  thf(t175_relat_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( v1_relat_1 @ C ) =>
% 0.61/0.81       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.61/0.81         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.61/0.81  thf('4', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.61/0.81         (((k10_relat_1 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.61/0.81            = (k2_xboole_0 @ (k10_relat_1 @ X15 @ X16) @ 
% 0.61/0.81               (k10_relat_1 @ X15 @ X17)))
% 0.61/0.81          | ~ (v1_relat_1 @ X15))),
% 0.61/0.81      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.61/0.81  thf('5', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t146_funct_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( v1_relat_1 @ B ) =>
% 0.61/0.81       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.61/0.81         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.61/0.81  thf('6', plain,
% 0.61/0.81      (![X18 : $i, X19 : $i]:
% 0.61/0.81         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.61/0.81          | (r1_tarski @ X18 @ (k10_relat_1 @ X19 @ (k9_relat_1 @ X19 @ X18)))
% 0.61/0.81          | ~ (v1_relat_1 @ X19))),
% 0.61/0.81      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.61/0.81  thf('7', plain,
% 0.61/0.81      ((~ (v1_relat_1 @ sk_C)
% 0.61/0.81        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.81  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.61/0.81      inference('demod', [status(thm)], ['7', '8'])).
% 0.61/0.81  thf('10', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i]:
% 0.61/0.81         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.81  thf('11', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.61/0.81         = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.81  thf(t7_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('12', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.61/0.81  thf('13', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i]:
% 0.61/0.81         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.81  thf('14', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k2_xboole_0 @ X1 @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.81  thf('15', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.61/0.81  thf(t9_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( r1_tarski @ A @ B ) =>
% 0.61/0.81       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.61/0.81  thf('16', plain,
% 0.61/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.81         (~ (r1_tarski @ X12 @ X13)
% 0.61/0.81          | (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ (k2_xboole_0 @ X13 @ X14)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.61/0.81  thf('17', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         (r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ 
% 0.61/0.81          (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.61/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.81  thf(d10_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.81  thf('18', plain,
% 0.61/0.81      (![X0 : $i, X2 : $i]:
% 0.61/0.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.61/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.81  thf('19', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.61/0.81             (k2_xboole_0 @ X2 @ X0))
% 0.61/0.81          | ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 0.61/0.81              = (k2_xboole_0 @ X2 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.61/0.81             (k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))
% 0.61/0.81          | ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 0.61/0.81              (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 0.61/0.81              = (k2_xboole_0 @ X2 @ 
% 0.61/0.81                 (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['14', '19'])).
% 0.61/0.81  thf(t36_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.81  thf('21', plain,
% 0.61/0.81      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.61/0.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.81  thf(t44_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.61/0.81       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.61/0.81  thf('22', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.61/0.81         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.61/0.81          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.61/0.81      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.61/0.81  thf('23', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['21', '22'])).
% 0.61/0.81  thf('24', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k2_xboole_0 @ X1 @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.81  thf('25', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 0.61/0.81           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['20', '23', '24'])).
% 0.61/0.81  thf('26', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.61/0.81  thf('27', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['25', '26'])).
% 0.61/0.81  thf('28', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (r1_tarski @ sk_A @ 
% 0.61/0.81          (k2_xboole_0 @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['11', '27'])).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_A @ 
% 0.61/0.81           (k10_relat_1 @ sk_C @ 
% 0.61/0.81            (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ X0)))
% 0.61/0.81          | ~ (v1_relat_1 @ sk_C))),
% 0.61/0.81      inference('sup+', [status(thm)], ['4', '28'])).
% 0.61/0.81  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('31', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (r1_tarski @ sk_A @ 
% 0.61/0.81          (k10_relat_1 @ sk_C @ (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['29', '30'])).
% 0.61/0.81  thf('32', plain, ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.61/0.81      inference('sup+', [status(thm)], ['3', '31'])).
% 0.61/0.81  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.61/0.81  
% 0.61/0.81  % SZS output end Refutation
% 0.61/0.81  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
