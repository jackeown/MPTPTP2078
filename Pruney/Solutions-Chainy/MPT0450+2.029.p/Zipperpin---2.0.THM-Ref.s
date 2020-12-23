%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qm29jn2Mei

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:05 EST 2020

% Result     : Theorem 9.29s
% Output     : Refutation 9.29s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 103 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  403 ( 772 expanded)
%              Number of equality atoms :   11 (  39 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k3_relat_1 @ X23 ) @ ( k3_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k3_relat_1 @ X23 ) @ ( k3_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qm29jn2Mei
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.29/9.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.29/9.55  % Solved by: fo/fo7.sh
% 9.29/9.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.29/9.55  % done 9897 iterations in 9.101s
% 9.29/9.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.29/9.55  % SZS output start Refutation
% 9.29/9.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.29/9.55  thf(sk_A_type, type, sk_A: $i).
% 9.29/9.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.29/9.55  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 9.29/9.55  thf(sk_B_type, type, sk_B: $i).
% 9.29/9.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.29/9.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.29/9.55  thf(d10_xboole_0, axiom,
% 9.29/9.55    (![A:$i,B:$i]:
% 9.29/9.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.29/9.55  thf('0', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.29/9.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.29/9.55  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.29/9.55      inference('simplify', [status(thm)], ['0'])).
% 9.29/9.55  thf(t12_xboole_1, axiom,
% 9.29/9.55    (![A:$i,B:$i]:
% 9.29/9.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 9.29/9.55  thf('2', plain,
% 9.29/9.55      (![X6 : $i, X7 : $i]:
% 9.29/9.55         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 9.29/9.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.29/9.55  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 9.29/9.55      inference('sup-', [status(thm)], ['1', '2'])).
% 9.29/9.55  thf(t31_xboole_1, axiom,
% 9.29/9.55    (![A:$i,B:$i,C:$i]:
% 9.29/9.55     ( r1_tarski @
% 9.29/9.55       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 9.29/9.55       ( k2_xboole_0 @ B @ C ) ))).
% 9.29/9.55  thf('4', plain,
% 9.29/9.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.29/9.55         (r1_tarski @ 
% 9.29/9.55          (k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k3_xboole_0 @ X13 @ X15)) @ 
% 9.29/9.55          (k2_xboole_0 @ X14 @ X15))),
% 9.29/9.55      inference('cnf', [status(esa)], [t31_xboole_1])).
% 9.29/9.55  thf('5', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (r1_tarski @ 
% 9.29/9.55          (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.29/9.55          X0)),
% 9.29/9.55      inference('sup+', [status(thm)], ['3', '4'])).
% 9.29/9.55  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 9.29/9.55      inference('sup-', [status(thm)], ['1', '2'])).
% 9.29/9.55  thf('7', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.29/9.55      inference('demod', [status(thm)], ['5', '6'])).
% 9.29/9.55  thf('8', plain,
% 9.29/9.55      (![X6 : $i, X7 : $i]:
% 9.29/9.55         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 9.29/9.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.29/9.55  thf('9', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 9.29/9.55      inference('sup-', [status(thm)], ['7', '8'])).
% 9.29/9.55  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.29/9.55      inference('simplify', [status(thm)], ['0'])).
% 9.29/9.55  thf(t7_xboole_1, axiom,
% 9.29/9.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 9.29/9.55  thf('11', plain,
% 9.29/9.55      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 9.29/9.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.29/9.55  thf(t19_xboole_1, axiom,
% 9.29/9.55    (![A:$i,B:$i,C:$i]:
% 9.29/9.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 9.29/9.55       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 9.29/9.55  thf('12', plain,
% 9.29/9.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.29/9.55         (~ (r1_tarski @ X10 @ X11)
% 9.29/9.55          | ~ (r1_tarski @ X10 @ X12)
% 9.29/9.55          | (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 9.29/9.55      inference('cnf', [status(esa)], [t19_xboole_1])).
% 9.29/9.55  thf('13', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.29/9.55         ((r1_tarski @ X1 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 9.29/9.55          | ~ (r1_tarski @ X1 @ X2))),
% 9.29/9.55      inference('sup-', [status(thm)], ['11', '12'])).
% 9.29/9.55  thf('14', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (r1_tarski @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 9.29/9.55      inference('sup-', [status(thm)], ['10', '13'])).
% 9.29/9.55  thf('15', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.29/9.55      inference('demod', [status(thm)], ['5', '6'])).
% 9.29/9.55  thf('16', plain,
% 9.29/9.55      (![X0 : $i, X2 : $i]:
% 9.29/9.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.29/9.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.29/9.55  thf('17', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.29/9.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 9.29/9.55      inference('sup-', [status(thm)], ['15', '16'])).
% 9.29/9.55  thf('18', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 9.29/9.55      inference('sup-', [status(thm)], ['14', '17'])).
% 9.29/9.55  thf(fc1_relat_1, axiom,
% 9.29/9.55    (![A:$i,B:$i]:
% 9.29/9.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.29/9.55  thf('19', plain,
% 9.29/9.55      (![X19 : $i, X20 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k3_xboole_0 @ X19 @ X20)))),
% 9.29/9.55      inference('cnf', [status(esa)], [fc1_relat_1])).
% 9.29/9.55  thf('20', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         ((v1_relat_1 @ X0) | ~ (v1_relat_1 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.29/9.55      inference('sup+', [status(thm)], ['18', '19'])).
% 9.29/9.55  thf('21', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.29/9.55      inference('sup-', [status(thm)], ['9', '20'])).
% 9.29/9.55  thf('22', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.29/9.55      inference('demod', [status(thm)], ['5', '6'])).
% 9.29/9.55  thf(t31_relat_1, axiom,
% 9.29/9.55    (![A:$i]:
% 9.29/9.55     ( ( v1_relat_1 @ A ) =>
% 9.29/9.55       ( ![B:$i]:
% 9.29/9.55         ( ( v1_relat_1 @ B ) =>
% 9.29/9.55           ( ( r1_tarski @ A @ B ) =>
% 9.29/9.55             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 9.29/9.55  thf('23', plain,
% 9.29/9.55      (![X22 : $i, X23 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X22)
% 9.29/9.55          | (r1_tarski @ (k3_relat_1 @ X23) @ (k3_relat_1 @ X22))
% 9.29/9.55          | ~ (r1_tarski @ X23 @ X22)
% 9.29/9.55          | ~ (v1_relat_1 @ X23))),
% 9.29/9.55      inference('cnf', [status(esa)], [t31_relat_1])).
% 9.29/9.55  thf('24', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 9.29/9.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.29/9.55             (k3_relat_1 @ X0))
% 9.29/9.55          | ~ (v1_relat_1 @ X0))),
% 9.29/9.55      inference('sup-', [status(thm)], ['22', '23'])).
% 9.29/9.55  thf('25', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X0)
% 9.29/9.55          | ~ (v1_relat_1 @ X0)
% 9.29/9.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.29/9.55             (k3_relat_1 @ X0)))),
% 9.29/9.55      inference('sup-', [status(thm)], ['21', '24'])).
% 9.29/9.55  thf('26', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.29/9.55           (k3_relat_1 @ X0))
% 9.29/9.55          | ~ (v1_relat_1 @ X0))),
% 9.29/9.55      inference('simplify', [status(thm)], ['25'])).
% 9.29/9.55  thf(t17_xboole_1, axiom,
% 9.29/9.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 9.29/9.55  thf('27', plain,
% 9.29/9.55      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 9.29/9.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 9.29/9.55  thf('28', plain,
% 9.29/9.55      (![X22 : $i, X23 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X22)
% 9.29/9.55          | (r1_tarski @ (k3_relat_1 @ X23) @ (k3_relat_1 @ X22))
% 9.29/9.55          | ~ (r1_tarski @ X23 @ X22)
% 9.29/9.55          | ~ (v1_relat_1 @ X23))),
% 9.29/9.55      inference('cnf', [status(esa)], [t31_relat_1])).
% 9.29/9.55  thf('29', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 9.29/9.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.29/9.55             (k3_relat_1 @ X0))
% 9.29/9.55          | ~ (v1_relat_1 @ X0))),
% 9.29/9.55      inference('sup-', [status(thm)], ['27', '28'])).
% 9.29/9.55  thf('30', plain,
% 9.29/9.55      (![X19 : $i, X20 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k3_xboole_0 @ X19 @ X20)))),
% 9.29/9.55      inference('cnf', [status(esa)], [fc1_relat_1])).
% 9.29/9.55  thf('31', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X0)
% 9.29/9.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.29/9.55             (k3_relat_1 @ X0)))),
% 9.29/9.55      inference('clc', [status(thm)], ['29', '30'])).
% 9.29/9.55  thf('32', plain,
% 9.29/9.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.29/9.55         (~ (r1_tarski @ X10 @ X11)
% 9.29/9.55          | ~ (r1_tarski @ X10 @ X12)
% 9.29/9.55          | (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 9.29/9.55      inference('cnf', [status(esa)], [t19_xboole_1])).
% 9.29/9.55  thf('33', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X0)
% 9.29/9.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.29/9.55             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 9.29/9.55          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 9.29/9.55      inference('sup-', [status(thm)], ['31', '32'])).
% 9.29/9.55  thf('34', plain,
% 9.29/9.55      (![X0 : $i, X1 : $i]:
% 9.29/9.55         (~ (v1_relat_1 @ X0)
% 9.29/9.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.29/9.55             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 9.29/9.55          | ~ (v1_relat_1 @ X1))),
% 9.29/9.55      inference('sup-', [status(thm)], ['26', '33'])).
% 9.29/9.55  thf(t34_relat_1, conjecture,
% 9.29/9.55    (![A:$i]:
% 9.29/9.55     ( ( v1_relat_1 @ A ) =>
% 9.29/9.55       ( ![B:$i]:
% 9.29/9.55         ( ( v1_relat_1 @ B ) =>
% 9.29/9.55           ( r1_tarski @
% 9.29/9.55             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 9.29/9.55             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 9.29/9.55  thf(zf_stmt_0, negated_conjecture,
% 9.29/9.55    (~( ![A:$i]:
% 9.29/9.55        ( ( v1_relat_1 @ A ) =>
% 9.29/9.55          ( ![B:$i]:
% 9.29/9.55            ( ( v1_relat_1 @ B ) =>
% 9.29/9.55              ( r1_tarski @
% 9.29/9.55                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 9.29/9.55                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 9.29/9.55    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 9.29/9.55  thf('35', plain,
% 9.29/9.55      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 9.29/9.55          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 9.29/9.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.29/9.55  thf('36', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 9.29/9.55      inference('sup-', [status(thm)], ['34', '35'])).
% 9.29/9.55  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 9.29/9.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.29/9.55  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 9.29/9.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.29/9.55  thf('39', plain, ($false),
% 9.29/9.55      inference('demod', [status(thm)], ['36', '37', '38'])).
% 9.29/9.55  
% 9.29/9.55  % SZS output end Refutation
% 9.29/9.55  
% 9.42/9.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
