%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1wboyOVT71

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:49 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   55 (  83 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 ( 835 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ X24 @ ( k10_relat_1 @ X24 @ X23 ) )
        = ( k3_xboole_0 @ X23 @ ( k9_relat_1 @ X24 @ ( k1_relat_1 @ X24 ) ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ ( k10_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('10',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k9_relat_1 @ X20 @ X18 ) @ ( k9_relat_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['8','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1wboyOVT71
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.91/1.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.09  % Solved by: fo/fo7.sh
% 0.91/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.09  % done 1103 iterations in 0.629s
% 0.91/1.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.09  % SZS output start Refutation
% 0.91/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.09  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.09  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.91/1.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.09  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.91/1.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(t158_funct_1, conjecture,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.09       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.91/1.09           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.91/1.09         ( r1_tarski @ A @ B ) ) ))).
% 0.91/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.09    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.09        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.09          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.91/1.09              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.91/1.09            ( r1_tarski @ A @ B ) ) ) )),
% 0.91/1.09    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.91/1.09  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf(t146_relat_1, axiom,
% 0.91/1.09    (![A:$i]:
% 0.91/1.09     ( ( v1_relat_1 @ A ) =>
% 0.91/1.09       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.91/1.09  thf('1', plain,
% 0.91/1.09      (![X17 : $i]:
% 0.91/1.09         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 0.91/1.09          | ~ (v1_relat_1 @ X17))),
% 0.91/1.09      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.91/1.09  thf(t148_funct_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.09       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.91/1.09         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.91/1.09  thf('2', plain,
% 0.91/1.09      (![X23 : $i, X24 : $i]:
% 0.91/1.09         (((k9_relat_1 @ X24 @ (k10_relat_1 @ X24 @ X23))
% 0.91/1.09            = (k3_xboole_0 @ X23 @ (k9_relat_1 @ X24 @ (k1_relat_1 @ X24))))
% 0.91/1.09          | ~ (v1_funct_1 @ X24)
% 0.91/1.09          | ~ (v1_relat_1 @ X24))),
% 0.91/1.09      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.91/1.09  thf('3', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.91/1.09            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.91/1.09          | ~ (v1_relat_1 @ X0)
% 0.91/1.09          | ~ (v1_relat_1 @ X0)
% 0.91/1.09          | ~ (v1_funct_1 @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['1', '2'])).
% 0.91/1.09  thf('4', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (~ (v1_funct_1 @ X0)
% 0.91/1.09          | ~ (v1_relat_1 @ X0)
% 0.91/1.09          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.91/1.09              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.91/1.09      inference('simplify', [status(thm)], ['3'])).
% 0.91/1.09  thf(t145_funct_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.09       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.91/1.09  thf('5', plain,
% 0.91/1.09      (![X21 : $i, X22 : $i]:
% 0.91/1.09         ((r1_tarski @ (k9_relat_1 @ X21 @ (k10_relat_1 @ X21 @ X22)) @ X22)
% 0.91/1.09          | ~ (v1_funct_1 @ X21)
% 0.91/1.09          | ~ (v1_relat_1 @ X21))),
% 0.91/1.09      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.91/1.09  thf('6', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)) @ X1)
% 0.91/1.09          | ~ (v1_relat_1 @ X0)
% 0.91/1.09          | ~ (v1_funct_1 @ X0)
% 0.91/1.09          | ~ (v1_relat_1 @ X0)
% 0.91/1.09          | ~ (v1_funct_1 @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['4', '5'])).
% 0.91/1.09  thf('7', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (~ (v1_funct_1 @ X0)
% 0.91/1.09          | ~ (v1_relat_1 @ X0)
% 0.91/1.09          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)) @ X1))),
% 0.91/1.09      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.09  thf('8', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (~ (v1_funct_1 @ X0)
% 0.91/1.09          | ~ (v1_relat_1 @ X0)
% 0.91/1.09          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.91/1.09              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.91/1.09      inference('simplify', [status(thm)], ['3'])).
% 0.91/1.09  thf('9', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (~ (v1_funct_1 @ X0)
% 0.91/1.09          | ~ (v1_relat_1 @ X0)
% 0.91/1.09          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.91/1.09              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.91/1.09      inference('simplify', [status(thm)], ['3'])).
% 0.91/1.09  thf('10', plain,
% 0.91/1.09      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf(t156_relat_1, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( v1_relat_1 @ C ) =>
% 0.91/1.09       ( ( r1_tarski @ A @ B ) =>
% 0.91/1.09         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.91/1.09  thf('11', plain,
% 0.91/1.09      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.91/1.09         (~ (r1_tarski @ X18 @ X19)
% 0.91/1.09          | ~ (v1_relat_1 @ X20)
% 0.91/1.09          | (r1_tarski @ (k9_relat_1 @ X20 @ X18) @ (k9_relat_1 @ X20 @ X19)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.91/1.09  thf('12', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 0.91/1.09           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.91/1.09          | ~ (v1_relat_1 @ X0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['10', '11'])).
% 0.91/1.09  thf('13', plain,
% 0.91/1.09      (((r1_tarski @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) @ 
% 0.91/1.09         (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.91/1.09        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.09        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.09        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.09      inference('sup+', [status(thm)], ['9', '12'])).
% 0.91/1.09  thf('14', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf(t28_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.09  thf('15', plain,
% 0.91/1.09      (![X10 : $i, X11 : $i]:
% 0.91/1.09         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.91/1.09      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.09  thf('16', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 0.91/1.09      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.09  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('20', plain,
% 0.91/1.09      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.91/1.09      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 0.91/1.09  thf('21', plain,
% 0.91/1.09      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.91/1.09        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.09        | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.09      inference('sup+', [status(thm)], ['8', '20'])).
% 0.91/1.09  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('24', plain,
% 0.91/1.09      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.91/1.09      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.91/1.09  thf(t12_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.09  thf('25', plain,
% 0.91/1.09      (![X8 : $i, X9 : $i]:
% 0.91/1.09         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.91/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.09  thf('26', plain,
% 0.91/1.09      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.91/1.09         = (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['24', '25'])).
% 0.91/1.09  thf(t11_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.91/1.09  thf('27', plain,
% 0.91/1.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.09         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.91/1.09      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.91/1.09  thf('28', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) @ X0)
% 0.91/1.09          | (r1_tarski @ sk_A @ X0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.09  thf('29', plain,
% 0.91/1.09      ((~ (v1_relat_1 @ sk_C)
% 0.91/1.09        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.09        | (r1_tarski @ sk_A @ sk_B))),
% 0.91/1.09      inference('sup-', [status(thm)], ['7', '28'])).
% 0.91/1.09  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('32', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.91/1.09      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.91/1.09  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.91/1.09  
% 0.91/1.09  % SZS output end Refutation
% 0.91/1.09  
% 0.91/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
