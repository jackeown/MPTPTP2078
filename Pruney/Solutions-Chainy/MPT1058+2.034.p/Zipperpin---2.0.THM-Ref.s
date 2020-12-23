%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jqgVAvYKGx

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:41 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  339 ( 444 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k3_xboole_0 @ X19 @ ( k10_relat_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('25',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jqgVAvYKGx
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 430 iterations in 0.166s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(t175_funct_2, conjecture,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62       ( ![B:$i,C:$i]:
% 0.40/0.62         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.40/0.62           ( ( k10_relat_1 @ A @ C ) =
% 0.40/0.62             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i]:
% 0.40/0.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62          ( ![B:$i,C:$i]:
% 0.40/0.62            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.40/0.62              ( ( k10_relat_1 @ A @ C ) =
% 0.40/0.62                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.40/0.62  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t3_boole, axiom,
% 0.40/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.62  thf('1', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.62  thf(t36_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.40/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.62  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.62      inference('sup+', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf(t19_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.40/0.62       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X2 @ X3)
% 0.40/0.62          | ~ (r1_tarski @ X2 @ X4)
% 0.40/0.62          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.40/0.62        (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '5'])).
% 0.40/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.40/0.62        (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.40/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.62  thf(t1_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.40/0.62       ( r1_tarski @ A @ C ) ))).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X5 @ X6)
% 0.40/0.62          | ~ (r1_tarski @ X6 @ X7)
% 0.40/0.62          | (r1_tarski @ X5 @ X7))),
% 0.40/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (r1_tarski @ (k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ X0) @ 
% 0.40/0.62          (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['8', '11'])).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.62  thf(t48_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X13 : $i, X14 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.40/0.62           = (k3_xboole_0 @ X13 @ X14))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf(t38_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.40/0.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X10 : $i, X11 : $i]:
% 0.40/0.62         (((X10) = (k1_xboole_0))
% 0.40/0.62          | ~ (r1_tarski @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.62          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.62          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['13', '16'])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['12', '17'])).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X13 : $i, X14 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.40/0.62           = (k3_xboole_0 @ X13 @ X14))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ k1_xboole_0)
% 0.40/0.62         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.40/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('21', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (((k10_relat_1 @ sk_A @ sk_C)
% 0.40/0.62         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.40/0.62  thf(t139_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ C ) =>
% 0.40/0.62       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.40/0.62         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.62         (((k10_relat_1 @ (k7_relat_1 @ X20 @ X19) @ X21)
% 0.40/0.62            = (k3_xboole_0 @ X19 @ (k10_relat_1 @ X20 @ X21)))
% 0.40/0.62          | ~ (v1_relat_1 @ X20))),
% 0.40/0.62      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (((k10_relat_1 @ sk_A @ sk_C)
% 0.40/0.62         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.40/0.62          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.40/0.62        | ~ (v1_relat_1 @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.62  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (((k10_relat_1 @ sk_A @ sk_C)
% 0.40/0.62         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.62  thf('29', plain, ($false),
% 0.40/0.62      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
