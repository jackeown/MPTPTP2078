%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TOQrk18Obr

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:06 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   52 (  64 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  389 ( 573 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X29 @ X30 ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k9_relat_1 @ X47 @ ( k10_relat_1 @ X47 @ X46 ) )
        = ( k3_xboole_0 @ X46 @ ( k9_relat_1 @ X47 @ ( k1_relat_1 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ ( k6_subset_1 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X16 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','9'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( v1_relat_1 @ X50 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v2_funct_1 @ X50 )
      | ~ ( r1_tarski @ X48 @ ( k1_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X50 @ X48 ) @ ( k9_relat_1 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ X42 @ ( k1_relat_1 @ X43 ) )
      | ( r1_tarski @ X42 @ ( k10_relat_1 @ X43 @ ( k9_relat_1 @ X43 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['25','26','27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TOQrk18Obr
% 0.13/0.36  % Computer   : n014.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:46:52 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.44/3.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.44/3.63  % Solved by: fo/fo7.sh
% 3.44/3.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.44/3.63  % done 3262 iterations in 3.165s
% 3.44/3.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.44/3.63  % SZS output start Refutation
% 3.44/3.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.44/3.63  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.44/3.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.44/3.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.44/3.63  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.44/3.63  thf(sk_A_type, type, sk_A: $i).
% 3.44/3.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.44/3.63  thf(sk_B_type, type, sk_B: $i).
% 3.44/3.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.44/3.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.44/3.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.44/3.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.44/3.63  thf(t167_relat_1, axiom,
% 3.44/3.63    (![A:$i,B:$i]:
% 3.44/3.63     ( ( v1_relat_1 @ B ) =>
% 3.44/3.63       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 3.44/3.63  thf('0', plain,
% 3.44/3.63      (![X29 : $i, X30 : $i]:
% 3.44/3.63         ((r1_tarski @ (k10_relat_1 @ X29 @ X30) @ (k1_relat_1 @ X29))
% 3.44/3.63          | ~ (v1_relat_1 @ X29))),
% 3.44/3.63      inference('cnf', [status(esa)], [t167_relat_1])).
% 3.44/3.63  thf(t148_funct_1, axiom,
% 3.44/3.63    (![A:$i,B:$i]:
% 3.44/3.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.44/3.63       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 3.44/3.63         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 3.44/3.63  thf('1', plain,
% 3.44/3.63      (![X46 : $i, X47 : $i]:
% 3.44/3.63         (((k9_relat_1 @ X47 @ (k10_relat_1 @ X47 @ X46))
% 3.44/3.63            = (k3_xboole_0 @ X46 @ (k9_relat_1 @ X47 @ (k1_relat_1 @ X47))))
% 3.44/3.63          | ~ (v1_funct_1 @ X47)
% 3.44/3.63          | ~ (v1_relat_1 @ X47))),
% 3.44/3.63      inference('cnf', [status(esa)], [t148_funct_1])).
% 3.44/3.63  thf(t48_xboole_1, axiom,
% 3.44/3.63    (![A:$i,B:$i]:
% 3.44/3.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.44/3.63  thf('2', plain,
% 3.44/3.63      (![X20 : $i, X21 : $i]:
% 3.44/3.63         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 3.44/3.63           = (k3_xboole_0 @ X20 @ X21))),
% 3.44/3.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.44/3.63  thf(redefinition_k6_subset_1, axiom,
% 3.44/3.63    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.44/3.63  thf('3', plain,
% 3.44/3.63      (![X24 : $i, X25 : $i]:
% 3.44/3.63         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 3.44/3.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.44/3.63  thf('4', plain,
% 3.44/3.63      (![X24 : $i, X25 : $i]:
% 3.44/3.63         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 3.44/3.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.44/3.63  thf('5', plain,
% 3.44/3.63      (![X20 : $i, X21 : $i]:
% 3.44/3.63         ((k6_subset_1 @ X20 @ (k6_subset_1 @ X20 @ X21))
% 3.44/3.63           = (k3_xboole_0 @ X20 @ X21))),
% 3.44/3.63      inference('demod', [status(thm)], ['2', '3', '4'])).
% 3.44/3.63  thf(t36_xboole_1, axiom,
% 3.44/3.63    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.44/3.63  thf('6', plain,
% 3.44/3.63      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 3.44/3.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.44/3.63  thf('7', plain,
% 3.44/3.63      (![X24 : $i, X25 : $i]:
% 3.44/3.63         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 3.44/3.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.44/3.63  thf('8', plain,
% 3.44/3.63      (![X16 : $i, X17 : $i]: (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X16)),
% 3.44/3.63      inference('demod', [status(thm)], ['6', '7'])).
% 3.44/3.63  thf('9', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 3.44/3.63      inference('sup+', [status(thm)], ['5', '8'])).
% 3.44/3.63  thf('10', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 3.44/3.63          | ~ (v1_relat_1 @ X1)
% 3.44/3.63          | ~ (v1_funct_1 @ X1))),
% 3.44/3.63      inference('sup+', [status(thm)], ['1', '9'])).
% 3.44/3.63  thf(t157_funct_1, axiom,
% 3.44/3.63    (![A:$i,B:$i,C:$i]:
% 3.44/3.63     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.44/3.63       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 3.44/3.63           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 3.44/3.63         ( r1_tarski @ A @ B ) ) ))).
% 3.44/3.63  thf('11', plain,
% 3.44/3.63      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.44/3.63         ((r1_tarski @ X48 @ X49)
% 3.44/3.63          | ~ (v1_relat_1 @ X50)
% 3.44/3.63          | ~ (v1_funct_1 @ X50)
% 3.44/3.63          | ~ (v2_funct_1 @ X50)
% 3.44/3.63          | ~ (r1_tarski @ X48 @ (k1_relat_1 @ X50))
% 3.44/3.63          | ~ (r1_tarski @ (k9_relat_1 @ X50 @ X48) @ (k9_relat_1 @ X50 @ X49)))),
% 3.44/3.63      inference('cnf', [status(esa)], [t157_funct_1])).
% 3.44/3.63  thf('12', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         (~ (v1_funct_1 @ X1)
% 3.44/3.63          | ~ (v1_relat_1 @ X1)
% 3.44/3.63          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 3.44/3.63               (k1_relat_1 @ X1))
% 3.44/3.63          | ~ (v2_funct_1 @ X1)
% 3.44/3.63          | ~ (v1_funct_1 @ X1)
% 3.44/3.63          | ~ (v1_relat_1 @ X1)
% 3.44/3.63          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['10', '11'])).
% 3.44/3.63  thf('13', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 3.44/3.63          | ~ (v2_funct_1 @ X1)
% 3.44/3.63          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 3.44/3.63               (k1_relat_1 @ X1))
% 3.44/3.63          | ~ (v1_relat_1 @ X1)
% 3.44/3.63          | ~ (v1_funct_1 @ X1))),
% 3.44/3.63      inference('simplify', [status(thm)], ['12'])).
% 3.44/3.63  thf('14', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         (~ (v1_relat_1 @ X0)
% 3.44/3.63          | ~ (v1_funct_1 @ X0)
% 3.44/3.63          | ~ (v1_relat_1 @ X0)
% 3.44/3.63          | ~ (v2_funct_1 @ X0)
% 3.44/3.63          | (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X1))),
% 3.44/3.63      inference('sup-', [status(thm)], ['0', '13'])).
% 3.44/3.63  thf('15', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 3.44/3.63          | ~ (v2_funct_1 @ X0)
% 3.44/3.63          | ~ (v1_funct_1 @ X0)
% 3.44/3.63          | ~ (v1_relat_1 @ X0))),
% 3.44/3.63      inference('simplify', [status(thm)], ['14'])).
% 3.44/3.63  thf(t164_funct_1, conjecture,
% 3.44/3.63    (![A:$i,B:$i]:
% 3.44/3.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.44/3.63       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 3.44/3.63         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.44/3.63  thf(zf_stmt_0, negated_conjecture,
% 3.44/3.63    (~( ![A:$i,B:$i]:
% 3.44/3.63        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.44/3.63          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 3.44/3.63            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 3.44/3.63    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 3.44/3.63  thf('16', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf(t146_funct_1, axiom,
% 3.44/3.63    (![A:$i,B:$i]:
% 3.44/3.63     ( ( v1_relat_1 @ B ) =>
% 3.44/3.63       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.44/3.63         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 3.44/3.63  thf('17', plain,
% 3.44/3.63      (![X42 : $i, X43 : $i]:
% 3.44/3.63         (~ (r1_tarski @ X42 @ (k1_relat_1 @ X43))
% 3.44/3.63          | (r1_tarski @ X42 @ (k10_relat_1 @ X43 @ (k9_relat_1 @ X43 @ X42)))
% 3.44/3.63          | ~ (v1_relat_1 @ X43))),
% 3.44/3.63      inference('cnf', [status(esa)], [t146_funct_1])).
% 3.44/3.63  thf('18', plain,
% 3.44/3.63      ((~ (v1_relat_1 @ sk_B)
% 3.44/3.63        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 3.44/3.63      inference('sup-', [status(thm)], ['16', '17'])).
% 3.44/3.63  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('20', plain,
% 3.44/3.63      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 3.44/3.63      inference('demod', [status(thm)], ['18', '19'])).
% 3.44/3.63  thf(d10_xboole_0, axiom,
% 3.44/3.63    (![A:$i,B:$i]:
% 3.44/3.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.44/3.63  thf('21', plain,
% 3.44/3.63      (![X12 : $i, X14 : $i]:
% 3.44/3.63         (((X12) = (X14))
% 3.44/3.63          | ~ (r1_tarski @ X14 @ X12)
% 3.44/3.63          | ~ (r1_tarski @ X12 @ X14))),
% 3.44/3.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.44/3.63  thf('22', plain,
% 3.44/3.63      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 3.44/3.63        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 3.44/3.63      inference('sup-', [status(thm)], ['20', '21'])).
% 3.44/3.63  thf('23', plain,
% 3.44/3.63      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('24', plain,
% 3.44/3.63      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 3.44/3.63      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 3.44/3.63  thf('25', plain,
% 3.44/3.63      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 3.44/3.63      inference('sup-', [status(thm)], ['15', '24'])).
% 3.44/3.63  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('28', plain, ((v2_funct_1 @ sk_B)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('29', plain, ($false),
% 3.44/3.63      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 3.44/3.63  
% 3.44/3.63  % SZS output end Refutation
% 3.44/3.63  
% 3.44/3.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
