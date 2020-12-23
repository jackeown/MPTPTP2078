%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pQHSD3xD4d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:49 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  384 ( 586 expanded)
%              Number of equality atoms :   31 (  34 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k6_subset_1 @ X20 @ X21 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X19 @ X20 ) @ ( k10_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( k2_relat_1 @ X18 ) )
      | ( ( k10_relat_1 @ X18 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k6_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k6_subset_1 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pQHSD3xD4d
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:08:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.50  % Solved by: fo/fo7.sh
% 0.18/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.50  % done 126 iterations in 0.059s
% 0.18/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.50  % SZS output start Refutation
% 0.18/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.18/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.18/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.50  thf(t158_funct_1, conjecture,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.18/0.50       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.18/0.50           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.18/0.50         ( r1_tarski @ A @ B ) ) ))).
% 0.18/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.50        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.18/0.50          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.18/0.50              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.18/0.50            ( r1_tarski @ A @ B ) ) ) )),
% 0.18/0.50    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.18/0.50  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf(t138_funct_1, axiom,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.18/0.50       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.18/0.50         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.18/0.50  thf('1', plain,
% 0.18/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.18/0.50         (((k10_relat_1 @ X19 @ (k6_subset_1 @ X20 @ X21))
% 0.18/0.50            = (k6_subset_1 @ (k10_relat_1 @ X19 @ X20) @ 
% 0.18/0.50               (k10_relat_1 @ X19 @ X21)))
% 0.18/0.50          | ~ (v1_funct_1 @ X19)
% 0.18/0.50          | ~ (v1_relat_1 @ X19))),
% 0.18/0.50      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.18/0.50  thf('2', plain,
% 0.18/0.50      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf(l32_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.50  thf('3', plain,
% 0.18/0.50      (![X2 : $i, X4 : $i]:
% 0.18/0.50         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.18/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.50  thf(redefinition_k6_subset_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.18/0.50  thf('4', plain,
% 0.18/0.50      (![X15 : $i, X16 : $i]:
% 0.18/0.50         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.18/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.18/0.50  thf('5', plain,
% 0.18/0.50      (![X2 : $i, X4 : $i]:
% 0.18/0.50         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.18/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.18/0.50  thf('6', plain,
% 0.18/0.50      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.18/0.50         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.18/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.18/0.50  thf('7', plain,
% 0.18/0.50      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.18/0.50        | ~ (v1_relat_1 @ sk_C)
% 0.18/0.50        | ~ (v1_funct_1 @ sk_C))),
% 0.18/0.50      inference('sup+', [status(thm)], ['1', '6'])).
% 0.18/0.50  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('10', plain,
% 0.18/0.50      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.18/0.50      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.18/0.50  thf(t7_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.50  thf('11', plain,
% 0.18/0.50      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.18/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.18/0.50  thf('12', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf(t12_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.18/0.50  thf('13', plain,
% 0.18/0.50      (![X8 : $i, X9 : $i]:
% 0.18/0.50         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.18/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.18/0.50  thf('14', plain,
% 0.18/0.50      (((k2_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.18/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.50  thf(t11_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.18/0.50  thf('15', plain,
% 0.18/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.18/0.50         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.18/0.50      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.18/0.50  thf('16', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.18/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.18/0.50  thf('17', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 0.18/0.50      inference('sup-', [status(thm)], ['11', '16'])).
% 0.18/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.18/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.18/0.50  thf('18', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.18/0.50  thf(t43_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.18/0.50       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.18/0.50  thf('19', plain,
% 0.18/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.50         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.18/0.50          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.18/0.50      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.18/0.50  thf('20', plain,
% 0.18/0.50      (![X15 : $i, X16 : $i]:
% 0.18/0.50         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.18/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.18/0.50  thf('21', plain,
% 0.18/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.50         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 0.18/0.50          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.18/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.50  thf('22', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.50         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.18/0.50          | (r1_tarski @ (k6_subset_1 @ X2 @ X0) @ X1))),
% 0.18/0.50      inference('sup-', [status(thm)], ['18', '21'])).
% 0.18/0.50  thf('23', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.18/0.50      inference('sup-', [status(thm)], ['17', '22'])).
% 0.18/0.50  thf(t174_relat_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( v1_relat_1 @ B ) =>
% 0.18/0.50       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.50            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.18/0.50            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.18/0.50  thf('24', plain,
% 0.18/0.50      (![X17 : $i, X18 : $i]:
% 0.18/0.50         (((X17) = (k1_xboole_0))
% 0.18/0.50          | ~ (v1_relat_1 @ X18)
% 0.18/0.50          | ~ (r1_tarski @ X17 @ (k2_relat_1 @ X18))
% 0.18/0.50          | ((k10_relat_1 @ X18 @ X17) != (k1_xboole_0)))),
% 0.18/0.50      inference('cnf', [status(esa)], [t174_relat_1])).
% 0.18/0.50  thf('25', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 0.18/0.50          | ~ (v1_relat_1 @ sk_C)
% 0.18/0.50          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.18/0.50  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('27', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 0.18/0.50          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.18/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.18/0.50  thf('28', plain,
% 0.18/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.50        | ((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['10', '27'])).
% 0.18/0.50  thf('29', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.18/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.18/0.50  thf('30', plain,
% 0.18/0.50      (![X2 : $i, X3 : $i]:
% 0.18/0.50         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.18/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.50  thf('31', plain,
% 0.18/0.50      (![X15 : $i, X16 : $i]:
% 0.18/0.50         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.18/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.18/0.50  thf('32', plain,
% 0.18/0.50      (![X2 : $i, X3 : $i]:
% 0.18/0.50         ((r1_tarski @ X2 @ X3) | ((k6_subset_1 @ X2 @ X3) != (k1_xboole_0)))),
% 0.18/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.18/0.50  thf('33', plain,
% 0.18/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.18/0.50      inference('sup-', [status(thm)], ['29', '32'])).
% 0.18/0.50  thf('34', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.18/0.50  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.18/0.50  
% 0.18/0.50  % SZS output end Refutation
% 0.18/0.50  
% 0.18/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
