%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N3xi5k6tuo

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:38 EST 2020

% Result     : Theorem 21.96s
% Output     : Refutation 21.96s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  434 ( 527 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k9_relat_1 @ X24 @ ( k6_subset_1 @ X25 @ X26 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X24 @ X25 ) @ ( k9_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k9_relat_1 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
        = ( k4_xboole_0 @ ( k9_relat_1 @ X24 @ X25 ) @ ( k9_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X31 ) ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k4_xboole_0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ X18 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ X0 @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t152_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_funct_1])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N3xi5k6tuo
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 21.96/22.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.96/22.14  % Solved by: fo/fo7.sh
% 21.96/22.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.96/22.14  % done 19146 iterations in 21.714s
% 21.96/22.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.96/22.14  % SZS output start Refutation
% 21.96/22.14  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 21.96/22.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.96/22.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.96/22.14  thf(sk_B_type, type, sk_B: $i).
% 21.96/22.14  thf(sk_A_type, type, sk_A: $i).
% 21.96/22.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 21.96/22.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.96/22.14  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 21.96/22.14  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 21.96/22.14  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 21.96/22.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.96/22.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 21.96/22.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 21.96/22.14  thf(t123_funct_1, axiom,
% 21.96/22.14    (![A:$i,B:$i,C:$i]:
% 21.96/22.14     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 21.96/22.14       ( ( v2_funct_1 @ C ) =>
% 21.96/22.14         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 21.96/22.14           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 21.96/22.14  thf('0', plain,
% 21.96/22.14      (![X24 : $i, X25 : $i, X26 : $i]:
% 21.96/22.14         (~ (v2_funct_1 @ X24)
% 21.96/22.14          | ((k9_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 21.96/22.14              = (k6_subset_1 @ (k9_relat_1 @ X24 @ X25) @ 
% 21.96/22.14                 (k9_relat_1 @ X24 @ X26)))
% 21.96/22.14          | ~ (v1_funct_1 @ X24)
% 21.96/22.14          | ~ (v1_relat_1 @ X24))),
% 21.96/22.14      inference('cnf', [status(esa)], [t123_funct_1])).
% 21.96/22.14  thf(redefinition_k6_subset_1, axiom,
% 21.96/22.14    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 21.96/22.14  thf('1', plain,
% 21.96/22.14      (![X15 : $i, X16 : $i]:
% 21.96/22.14         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 21.96/22.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 21.96/22.14  thf('2', plain,
% 21.96/22.14      (![X15 : $i, X16 : $i]:
% 21.96/22.14         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 21.96/22.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 21.96/22.14  thf('3', plain,
% 21.96/22.14      (![X24 : $i, X25 : $i, X26 : $i]:
% 21.96/22.14         (~ (v2_funct_1 @ X24)
% 21.96/22.14          | ((k9_relat_1 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 21.96/22.14              = (k4_xboole_0 @ (k9_relat_1 @ X24 @ X25) @ 
% 21.96/22.14                 (k9_relat_1 @ X24 @ X26)))
% 21.96/22.14          | ~ (v1_funct_1 @ X24)
% 21.96/22.14          | ~ (v1_relat_1 @ X24))),
% 21.96/22.14      inference('demod', [status(thm)], ['0', '1', '2'])).
% 21.96/22.14  thf(t145_funct_1, axiom,
% 21.96/22.14    (![A:$i,B:$i]:
% 21.96/22.14     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.96/22.14       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 21.96/22.14  thf('4', plain,
% 21.96/22.14      (![X30 : $i, X31 : $i]:
% 21.96/22.14         ((r1_tarski @ (k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X31)) @ X31)
% 21.96/22.14          | ~ (v1_funct_1 @ X30)
% 21.96/22.14          | ~ (v1_relat_1 @ X30))),
% 21.96/22.14      inference('cnf', [status(esa)], [t145_funct_1])).
% 21.96/22.14  thf(l32_xboole_1, axiom,
% 21.96/22.14    (![A:$i,B:$i]:
% 21.96/22.14     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 21.96/22.14  thf('5', plain,
% 21.96/22.14      (![X3 : $i, X5 : $i]:
% 21.96/22.14         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 21.96/22.14      inference('cnf', [status(esa)], [l32_xboole_1])).
% 21.96/22.14  thf('6', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i]:
% 21.96/22.14         (~ (v1_relat_1 @ X1)
% 21.96/22.14          | ~ (v1_funct_1 @ X1)
% 21.96/22.14          | ((k4_xboole_0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 21.96/22.14              = (k1_xboole_0)))),
% 21.96/22.14      inference('sup-', [status(thm)], ['4', '5'])).
% 21.96/22.14  thf('7', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i]:
% 21.96/22.14         (((k9_relat_1 @ X1 @ 
% 21.96/22.14            (k4_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 21.96/22.14            = (k1_xboole_0))
% 21.96/22.14          | ~ (v1_relat_1 @ X1)
% 21.96/22.14          | ~ (v1_funct_1 @ X1)
% 21.96/22.14          | ~ (v2_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_relat_1 @ X1))),
% 21.96/22.14      inference('sup+', [status(thm)], ['3', '6'])).
% 21.96/22.14  thf('8', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i]:
% 21.96/22.14         (~ (v2_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_relat_1 @ X1)
% 21.96/22.14          | ((k9_relat_1 @ X1 @ 
% 21.96/22.14              (k4_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 21.96/22.14              = (k1_xboole_0)))),
% 21.96/22.14      inference('simplify', [status(thm)], ['7'])).
% 21.96/22.14  thf(t167_relat_1, axiom,
% 21.96/22.14    (![A:$i,B:$i]:
% 21.96/22.14     ( ( v1_relat_1 @ B ) =>
% 21.96/22.14       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 21.96/22.14  thf('9', plain,
% 21.96/22.14      (![X19 : $i, X20 : $i]:
% 21.96/22.14         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 21.96/22.14          | ~ (v1_relat_1 @ X19))),
% 21.96/22.14      inference('cnf', [status(esa)], [t167_relat_1])).
% 21.96/22.14  thf(t36_xboole_1, axiom,
% 21.96/22.14    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 21.96/22.14  thf('10', plain,
% 21.96/22.14      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 21.96/22.14      inference('cnf', [status(esa)], [t36_xboole_1])).
% 21.96/22.14  thf(t12_xboole_1, axiom,
% 21.96/22.14    (![A:$i,B:$i]:
% 21.96/22.14     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 21.96/22.14  thf('11', plain,
% 21.96/22.14      (![X9 : $i, X10 : $i]:
% 21.96/22.14         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 21.96/22.14      inference('cnf', [status(esa)], [t12_xboole_1])).
% 21.96/22.14  thf('12', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i]:
% 21.96/22.14         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 21.96/22.14      inference('sup-', [status(thm)], ['10', '11'])).
% 21.96/22.14  thf(t11_xboole_1, axiom,
% 21.96/22.14    (![A:$i,B:$i,C:$i]:
% 21.96/22.14     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 21.96/22.14  thf('13', plain,
% 21.96/22.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.96/22.14         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 21.96/22.14      inference('cnf', [status(esa)], [t11_xboole_1])).
% 21.96/22.14  thf('14', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.96/22.14         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 21.96/22.14      inference('sup-', [status(thm)], ['12', '13'])).
% 21.96/22.14  thf('15', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.96/22.14         (~ (v1_relat_1 @ X0)
% 21.96/22.14          | (r1_tarski @ (k4_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 21.96/22.14             (k1_relat_1 @ X0)))),
% 21.96/22.14      inference('sup-', [status(thm)], ['9', '14'])).
% 21.96/22.14  thf(t152_relat_1, axiom,
% 21.96/22.14    (![A:$i,B:$i]:
% 21.96/22.14     ( ( v1_relat_1 @ B ) =>
% 21.96/22.14       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 21.96/22.14            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 21.96/22.14            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 21.96/22.14  thf('16', plain,
% 21.96/22.14      (![X17 : $i, X18 : $i]:
% 21.96/22.14         (((X17) = (k1_xboole_0))
% 21.96/22.14          | ~ (v1_relat_1 @ X18)
% 21.96/22.14          | ~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 21.96/22.14          | ((k9_relat_1 @ X18 @ X17) != (k1_xboole_0)))),
% 21.96/22.14      inference('cnf', [status(esa)], [t152_relat_1])).
% 21.96/22.14  thf('17', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.96/22.14         (~ (v1_relat_1 @ X0)
% 21.96/22.14          | ((k9_relat_1 @ X0 @ (k4_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 21.96/22.14              != (k1_xboole_0))
% 21.96/22.14          | ~ (v1_relat_1 @ X0)
% 21.96/22.14          | ((k4_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1) = (k1_xboole_0)))),
% 21.96/22.14      inference('sup-', [status(thm)], ['15', '16'])).
% 21.96/22.14  thf('18', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.96/22.14         (((k4_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1) = (k1_xboole_0))
% 21.96/22.14          | ((k9_relat_1 @ X0 @ (k4_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 21.96/22.14              != (k1_xboole_0))
% 21.96/22.14          | ~ (v1_relat_1 @ X0))),
% 21.96/22.14      inference('simplify', [status(thm)], ['17'])).
% 21.96/22.14  thf('19', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i]:
% 21.96/22.14         (((k1_xboole_0) != (k1_xboole_0))
% 21.96/22.14          | ~ (v1_relat_1 @ X1)
% 21.96/22.14          | ~ (v1_funct_1 @ X1)
% 21.96/22.14          | ~ (v2_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_relat_1 @ X1)
% 21.96/22.14          | ((k4_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 21.96/22.14              = (k1_xboole_0)))),
% 21.96/22.14      inference('sup-', [status(thm)], ['8', '18'])).
% 21.96/22.14  thf('20', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i]:
% 21.96/22.14         (((k4_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 21.96/22.14            = (k1_xboole_0))
% 21.96/22.14          | ~ (v2_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_relat_1 @ X1))),
% 21.96/22.14      inference('simplify', [status(thm)], ['19'])).
% 21.96/22.14  thf('21', plain,
% 21.96/22.14      (![X3 : $i, X4 : $i]:
% 21.96/22.14         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 21.96/22.14      inference('cnf', [status(esa)], [l32_xboole_1])).
% 21.96/22.14  thf('22', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i]:
% 21.96/22.14         (((k1_xboole_0) != (k1_xboole_0))
% 21.96/22.14          | ~ (v1_relat_1 @ X1)
% 21.96/22.14          | ~ (v1_funct_1 @ X1)
% 21.96/22.14          | ~ (v2_funct_1 @ X1)
% 21.96/22.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 21.96/22.14      inference('sup-', [status(thm)], ['20', '21'])).
% 21.96/22.14  thf('23', plain,
% 21.96/22.14      (![X0 : $i, X1 : $i]:
% 21.96/22.14         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 21.96/22.14          | ~ (v2_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_funct_1 @ X1)
% 21.96/22.14          | ~ (v1_relat_1 @ X1))),
% 21.96/22.14      inference('simplify', [status(thm)], ['22'])).
% 21.96/22.14  thf(t152_funct_1, conjecture,
% 21.96/22.14    (![A:$i,B:$i]:
% 21.96/22.14     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.96/22.14       ( ( v2_funct_1 @ B ) =>
% 21.96/22.14         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 21.96/22.14  thf(zf_stmt_0, negated_conjecture,
% 21.96/22.14    (~( ![A:$i,B:$i]:
% 21.96/22.14        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.96/22.14          ( ( v2_funct_1 @ B ) =>
% 21.96/22.14            ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )),
% 21.96/22.14    inference('cnf.neg', [status(esa)], [t152_funct_1])).
% 21.96/22.14  thf('24', plain,
% 21.96/22.14      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 21.96/22.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.96/22.14  thf('25', plain,
% 21.96/22.14      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 21.96/22.14      inference('sup-', [status(thm)], ['23', '24'])).
% 21.96/22.14  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 21.96/22.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.96/22.14  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 21.96/22.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.96/22.14  thf('28', plain, ((v2_funct_1 @ sk_B)),
% 21.96/22.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.96/22.14  thf('29', plain, ($false),
% 21.96/22.14      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 21.96/22.14  
% 21.96/22.14  % SZS output end Refutation
% 21.96/22.14  
% 21.98/22.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
