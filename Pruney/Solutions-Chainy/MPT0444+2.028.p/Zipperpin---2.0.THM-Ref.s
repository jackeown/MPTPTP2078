%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hPWe8H9cSj

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:49 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   54 (  88 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  384 ( 694 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ( r1_xboole_0 @ X33 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_tarski @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
      | ~ ( r1_xboole_0 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ( r1_tarski @ ( k2_relat_1 @ X58 ) @ ( k2_relat_1 @ X57 ) )
      | ~ ( r1_tarski @ X58 @ X57 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X51 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hPWe8H9cSj
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:25:36 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 2.04/2.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.04/2.25  % Solved by: fo/fo7.sh
% 2.04/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.04/2.25  % done 4426 iterations in 1.779s
% 2.04/2.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.04/2.25  % SZS output start Refutation
% 2.04/2.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.04/2.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.04/2.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.04/2.25  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.04/2.25  thf(sk_A_type, type, sk_A: $i).
% 2.04/2.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.04/2.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.04/2.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.04/2.25  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.04/2.25  thf(sk_B_type, type, sk_B: $i).
% 2.04/2.25  thf(t17_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.04/2.25  thf('0', plain,
% 2.04/2.25      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 2.04/2.25      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.04/2.25  thf(d10_xboole_0, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.04/2.25  thf('1', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.04/2.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.04/2.25  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.04/2.25      inference('simplify', [status(thm)], ['1'])).
% 2.04/2.25  thf(t85_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 2.04/2.25  thf('3', plain,
% 2.04/2.25      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.04/2.25         (~ (r1_tarski @ X33 @ X34)
% 2.04/2.25          | (r1_xboole_0 @ X33 @ (k4_xboole_0 @ X35 @ X34)))),
% 2.04/2.25      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.04/2.25  thf('4', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['2', '3'])).
% 2.04/2.25  thf(t31_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( r1_tarski @
% 2.04/2.25       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 2.04/2.25       ( k2_xboole_0 @ B @ C ) ))).
% 2.04/2.25  thf('5', plain,
% 2.04/2.25      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.04/2.25         (r1_tarski @ 
% 2.04/2.25          (k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k3_xboole_0 @ X21 @ X23)) @ 
% 2.04/2.25          (k2_xboole_0 @ X22 @ X23))),
% 2.04/2.25      inference('cnf', [status(esa)], [t31_xboole_1])).
% 2.04/2.25  thf(t11_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.04/2.25  thf('6', plain,
% 2.04/2.25      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.04/2.25         ((r1_tarski @ X12 @ X13)
% 2.04/2.25          | ~ (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ X13))),
% 2.04/2.25      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.04/2.25  thf('7', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.25         (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['5', '6'])).
% 2.04/2.25  thf(t73_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.04/2.25       ( r1_tarski @ A @ B ) ))).
% 2.04/2.25  thf('8', plain,
% 2.04/2.25      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.04/2.25         ((r1_tarski @ X30 @ X31)
% 2.04/2.25          | ~ (r1_tarski @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 2.04/2.25          | ~ (r1_xboole_0 @ X30 @ X32))),
% 2.04/2.25      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.04/2.25  thf('9', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.25         (~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 2.04/2.25          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['7', '8'])).
% 2.04/2.25  thf('10', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.04/2.25      inference('sup-', [status(thm)], ['4', '9'])).
% 2.04/2.25  thf(t19_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 2.04/2.25       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.04/2.25  thf('11', plain,
% 2.04/2.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.04/2.25         (~ (r1_tarski @ X17 @ X18)
% 2.04/2.25          | ~ (r1_tarski @ X17 @ X19)
% 2.04/2.25          | (r1_tarski @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 2.04/2.25      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.04/2.25  thf('12', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.25         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))
% 2.04/2.25          | ~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.04/2.25      inference('sup-', [status(thm)], ['10', '11'])).
% 2.04/2.25  thf('13', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['0', '12'])).
% 2.04/2.25  thf('14', plain,
% 2.04/2.25      (![X0 : $i, X2 : $i]:
% 2.04/2.25         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.04/2.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.04/2.25  thf('15', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 2.04/2.25          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['13', '14'])).
% 2.04/2.25  thf('16', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['0', '12'])).
% 2.04/2.25  thf('17', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.25      inference('demod', [status(thm)], ['15', '16'])).
% 2.04/2.25  thf('18', plain,
% 2.04/2.25      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 2.04/2.25      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.04/2.25  thf(t25_relat_1, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( v1_relat_1 @ A ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( v1_relat_1 @ B ) =>
% 2.04/2.25           ( ( r1_tarski @ A @ B ) =>
% 2.04/2.25             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 2.04/2.25               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 2.04/2.25  thf('19', plain,
% 2.04/2.25      (![X57 : $i, X58 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X57)
% 2.04/2.25          | (r1_tarski @ (k2_relat_1 @ X58) @ (k2_relat_1 @ X57))
% 2.04/2.25          | ~ (r1_tarski @ X58 @ X57)
% 2.04/2.25          | ~ (v1_relat_1 @ X58))),
% 2.04/2.25      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.04/2.25  thf('20', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.04/2.25          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.04/2.25             (k2_relat_1 @ X0))
% 2.04/2.25          | ~ (v1_relat_1 @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['18', '19'])).
% 2.04/2.25  thf(fc1_relat_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.04/2.25  thf('21', plain,
% 2.04/2.25      (![X51 : $i, X52 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X51) | (v1_relat_1 @ (k3_xboole_0 @ X51 @ X52)))),
% 2.04/2.25      inference('cnf', [status(esa)], [fc1_relat_1])).
% 2.04/2.25  thf('22', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X0)
% 2.04/2.25          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.04/2.25             (k2_relat_1 @ X0)))),
% 2.04/2.25      inference('clc', [status(thm)], ['20', '21'])).
% 2.04/2.25  thf('23', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.04/2.25           (k2_relat_1 @ X0))
% 2.04/2.25          | ~ (v1_relat_1 @ X0))),
% 2.04/2.25      inference('sup+', [status(thm)], ['17', '22'])).
% 2.04/2.25  thf('24', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X0)
% 2.04/2.25          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.04/2.25             (k2_relat_1 @ X0)))),
% 2.04/2.25      inference('clc', [status(thm)], ['20', '21'])).
% 2.04/2.25  thf('25', plain,
% 2.04/2.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.04/2.25         (~ (r1_tarski @ X17 @ X18)
% 2.04/2.25          | ~ (r1_tarski @ X17 @ X19)
% 2.04/2.25          | (r1_tarski @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 2.04/2.25      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.04/2.25  thf('26', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X0)
% 2.04/2.25          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.04/2.25             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 2.04/2.25          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 2.04/2.25      inference('sup-', [status(thm)], ['24', '25'])).
% 2.04/2.25  thf('27', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X0)
% 2.04/2.25          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.04/2.25             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 2.04/2.25          | ~ (v1_relat_1 @ X1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['23', '26'])).
% 2.04/2.25  thf(t27_relat_1, conjecture,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( v1_relat_1 @ A ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( v1_relat_1 @ B ) =>
% 2.04/2.25           ( r1_tarski @
% 2.04/2.25             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.04/2.25             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 2.04/2.25  thf(zf_stmt_0, negated_conjecture,
% 2.04/2.25    (~( ![A:$i]:
% 2.04/2.25        ( ( v1_relat_1 @ A ) =>
% 2.04/2.25          ( ![B:$i]:
% 2.04/2.25            ( ( v1_relat_1 @ B ) =>
% 2.04/2.25              ( r1_tarski @
% 2.04/2.25                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.04/2.25                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 2.04/2.25    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 2.04/2.25  thf('28', plain,
% 2.04/2.25      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 2.04/2.25          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('29', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['27', '28'])).
% 2.04/2.25  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('32', plain, ($false),
% 2.04/2.25      inference('demod', [status(thm)], ['29', '30', '31'])).
% 2.04/2.25  
% 2.04/2.25  % SZS output end Refutation
% 2.04/2.25  
% 2.04/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
