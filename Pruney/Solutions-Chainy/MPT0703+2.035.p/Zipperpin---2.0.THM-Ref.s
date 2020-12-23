%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GJsPR0HigI

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:53 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   55 (  83 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 ( 835 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X45: $i] :
      ( ( ( k9_relat_1 @ X45 @ ( k1_relat_1 @ X45 ) )
        = ( k2_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k9_relat_1 @ X52 @ ( k10_relat_1 @ X52 @ X51 ) )
        = ( k3_xboole_0 @ X51 @ ( k9_relat_1 @ X52 @ ( k1_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
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
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X49 @ ( k10_relat_1 @ X49 @ X50 ) ) @ X50 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ~ ( v1_relat_1 @ X48 )
      | ( r1_tarski @ ( k9_relat_1 @ X48 @ X46 ) @ ( k9_relat_1 @ X48 @ X47 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
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
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GJsPR0HigI
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:16:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.14/1.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.14/1.37  % Solved by: fo/fo7.sh
% 1.14/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.37  % done 1635 iterations in 0.908s
% 1.14/1.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.14/1.37  % SZS output start Refutation
% 1.14/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.14/1.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.14/1.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.14/1.37  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.14/1.37  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.14/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.37  thf(sk_C_type, type, sk_C: $i).
% 1.14/1.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.14/1.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.14/1.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.14/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.37  thf(t158_funct_1, conjecture,
% 1.14/1.37    (![A:$i,B:$i,C:$i]:
% 1.14/1.37     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.14/1.37       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 1.14/1.37           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 1.14/1.37         ( r1_tarski @ A @ B ) ) ))).
% 1.14/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.37    (~( ![A:$i,B:$i,C:$i]:
% 1.14/1.37        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.14/1.37          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 1.14/1.37              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 1.14/1.37            ( r1_tarski @ A @ B ) ) ) )),
% 1.14/1.37    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 1.14/1.37  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf(t146_relat_1, axiom,
% 1.14/1.37    (![A:$i]:
% 1.14/1.37     ( ( v1_relat_1 @ A ) =>
% 1.14/1.37       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.14/1.37  thf('1', plain,
% 1.14/1.37      (![X45 : $i]:
% 1.14/1.37         (((k9_relat_1 @ X45 @ (k1_relat_1 @ X45)) = (k2_relat_1 @ X45))
% 1.14/1.37          | ~ (v1_relat_1 @ X45))),
% 1.14/1.37      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.14/1.37  thf(t148_funct_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]:
% 1.14/1.37     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.37       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 1.14/1.37         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 1.14/1.37  thf('2', plain,
% 1.14/1.37      (![X51 : $i, X52 : $i]:
% 1.14/1.37         (((k9_relat_1 @ X52 @ (k10_relat_1 @ X52 @ X51))
% 1.14/1.37            = (k3_xboole_0 @ X51 @ (k9_relat_1 @ X52 @ (k1_relat_1 @ X52))))
% 1.14/1.37          | ~ (v1_funct_1 @ X52)
% 1.14/1.37          | ~ (v1_relat_1 @ X52))),
% 1.14/1.37      inference('cnf', [status(esa)], [t148_funct_1])).
% 1.14/1.37  thf('3', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 1.14/1.37            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 1.14/1.37          | ~ (v1_relat_1 @ X0)
% 1.14/1.37          | ~ (v1_relat_1 @ X0)
% 1.14/1.37          | ~ (v1_funct_1 @ X0))),
% 1.14/1.37      inference('sup+', [status(thm)], ['1', '2'])).
% 1.14/1.37  thf('4', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         (~ (v1_funct_1 @ X0)
% 1.14/1.37          | ~ (v1_relat_1 @ X0)
% 1.14/1.37          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 1.14/1.37              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 1.14/1.37      inference('simplify', [status(thm)], ['3'])).
% 1.14/1.37  thf(t145_funct_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]:
% 1.14/1.37     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.37       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.14/1.37  thf('5', plain,
% 1.14/1.37      (![X49 : $i, X50 : $i]:
% 1.14/1.37         ((r1_tarski @ (k9_relat_1 @ X49 @ (k10_relat_1 @ X49 @ X50)) @ X50)
% 1.14/1.37          | ~ (v1_funct_1 @ X49)
% 1.14/1.37          | ~ (v1_relat_1 @ X49))),
% 1.14/1.37      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.14/1.37  thf('6', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)) @ X1)
% 1.14/1.37          | ~ (v1_relat_1 @ X0)
% 1.14/1.37          | ~ (v1_funct_1 @ X0)
% 1.14/1.37          | ~ (v1_relat_1 @ X0)
% 1.14/1.37          | ~ (v1_funct_1 @ X0))),
% 1.14/1.37      inference('sup+', [status(thm)], ['4', '5'])).
% 1.14/1.37  thf('7', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         (~ (v1_funct_1 @ X0)
% 1.14/1.37          | ~ (v1_relat_1 @ X0)
% 1.14/1.37          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)) @ X1))),
% 1.14/1.37      inference('simplify', [status(thm)], ['6'])).
% 1.14/1.37  thf('8', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         (~ (v1_funct_1 @ X0)
% 1.14/1.37          | ~ (v1_relat_1 @ X0)
% 1.14/1.37          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 1.14/1.37              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 1.14/1.37      inference('simplify', [status(thm)], ['3'])).
% 1.14/1.37  thf('9', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         (~ (v1_funct_1 @ X0)
% 1.14/1.37          | ~ (v1_relat_1 @ X0)
% 1.14/1.37          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 1.14/1.37              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 1.14/1.37      inference('simplify', [status(thm)], ['3'])).
% 1.14/1.37  thf('10', plain,
% 1.14/1.37      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf(t156_relat_1, axiom,
% 1.14/1.37    (![A:$i,B:$i,C:$i]:
% 1.14/1.37     ( ( v1_relat_1 @ C ) =>
% 1.14/1.37       ( ( r1_tarski @ A @ B ) =>
% 1.14/1.37         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.14/1.37  thf('11', plain,
% 1.14/1.37      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.14/1.37         (~ (r1_tarski @ X46 @ X47)
% 1.14/1.37          | ~ (v1_relat_1 @ X48)
% 1.14/1.37          | (r1_tarski @ (k9_relat_1 @ X48 @ X46) @ (k9_relat_1 @ X48 @ X47)))),
% 1.14/1.37      inference('cnf', [status(esa)], [t156_relat_1])).
% 1.14/1.37  thf('12', plain,
% 1.14/1.37      (![X0 : $i]:
% 1.14/1.37         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 1.14/1.37           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)))
% 1.14/1.37          | ~ (v1_relat_1 @ X0))),
% 1.14/1.37      inference('sup-', [status(thm)], ['10', '11'])).
% 1.14/1.37  thf('13', plain,
% 1.14/1.37      (((r1_tarski @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) @ 
% 1.14/1.37         (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))
% 1.14/1.37        | ~ (v1_relat_1 @ sk_C)
% 1.14/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.14/1.37        | ~ (v1_relat_1 @ sk_C))),
% 1.14/1.37      inference('sup+', [status(thm)], ['9', '12'])).
% 1.14/1.37  thf('14', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf(t28_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]:
% 1.14/1.37     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.14/1.37  thf('15', plain,
% 1.14/1.37      (![X11 : $i, X12 : $i]:
% 1.14/1.37         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.14/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.14/1.37  thf('16', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 1.14/1.37      inference('sup-', [status(thm)], ['14', '15'])).
% 1.14/1.37  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf('20', plain,
% 1.14/1.37      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))),
% 1.14/1.37      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 1.14/1.37  thf('21', plain,
% 1.14/1.37      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))
% 1.14/1.37        | ~ (v1_relat_1 @ sk_C)
% 1.14/1.37        | ~ (v1_funct_1 @ sk_C))),
% 1.14/1.37      inference('sup+', [status(thm)], ['8', '20'])).
% 1.14/1.37  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf('24', plain,
% 1.14/1.37      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 1.14/1.37      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.14/1.37  thf(t12_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]:
% 1.14/1.37     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.14/1.37  thf('25', plain,
% 1.14/1.37      (![X9 : $i, X10 : $i]:
% 1.14/1.37         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 1.14/1.37      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.14/1.37  thf('26', plain,
% 1.14/1.37      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))
% 1.14/1.37         = (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 1.14/1.37      inference('sup-', [status(thm)], ['24', '25'])).
% 1.14/1.37  thf(t11_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i,C:$i]:
% 1.14/1.37     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.14/1.37  thf('27', plain,
% 1.14/1.37      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.14/1.37         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 1.14/1.37      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.14/1.37  thf('28', plain,
% 1.14/1.37      (![X0 : $i]:
% 1.14/1.37         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) @ X0)
% 1.14/1.37          | (r1_tarski @ sk_A @ X0))),
% 1.14/1.37      inference('sup-', [status(thm)], ['26', '27'])).
% 1.14/1.37  thf('29', plain,
% 1.14/1.37      ((~ (v1_relat_1 @ sk_C)
% 1.14/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.14/1.37        | (r1_tarski @ sk_A @ sk_B))),
% 1.14/1.37      inference('sup-', [status(thm)], ['7', '28'])).
% 1.14/1.37  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf('32', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.14/1.37      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.14/1.37  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 1.14/1.37  
% 1.14/1.37  % SZS output end Refutation
% 1.14/1.37  
% 1.14/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
