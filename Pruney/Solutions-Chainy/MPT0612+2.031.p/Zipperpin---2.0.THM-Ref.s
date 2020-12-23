%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hzMWfN7kTe

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:13 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   66 (  76 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  421 ( 519 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X5 @ X6 ) @ X5 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X10 @ X11 ) @ X11 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k6_subset_1 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k6_subset_1 @ X8 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X0 )
      | ( ( k6_subset_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','19'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ ( k6_subset_1 @ X13 @ X14 ) )
      | ~ ( r1_xboole_0 @ X13 @ ( k6_subset_1 @ X12 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k6_subset_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k6_subset_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X24 @ ( k7_relat_1 @ X24 @ X25 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k7_relat_1 @ X23 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k6_subset_1 @ X20 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hzMWfN7kTe
% 0.15/0.38  % Computer   : n004.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:51:54 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 410 iterations in 0.135s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.41/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.62  thf(t216_relat_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ C ) =>
% 0.41/0.62       ( ( r1_tarski @ A @ B ) =>
% 0.41/0.62         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.41/0.62           ( k1_xboole_0 ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.62        ( ( v1_relat_1 @ C ) =>
% 0.41/0.62          ( ( r1_tarski @ A @ B ) =>
% 0.41/0.62            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.41/0.62              ( k1_xboole_0 ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.41/0.62  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t36_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.41/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.41/0.62  thf(redefinition_k6_subset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i]: (r1_tarski @ (k6_subset_1 @ X5 @ X6) @ X5)),
% 0.41/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf(t1_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.41/0.62       ( r1_tarski @ A @ C ) ))).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X2 @ X3)
% 0.41/0.62          | ~ (r1_tarski @ X3 @ X4)
% 0.41/0.62          | (r1_tarski @ X2 @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.62  thf('6', plain, (![X0 : $i]: (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ sk_B)),
% 0.41/0.62      inference('sup-', [status(thm)], ['0', '5'])).
% 0.41/0.62  thf(t79_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 0.41/0.62      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.41/0.63  thf('9', plain,
% 0.41/0.63      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X10 @ X11) @ X11)),
% 0.41/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.63  thf(symmetry_r1_xboole_0, axiom,
% 0.41/0.63    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.41/0.63  thf('10', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.41/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.41/0.63  thf('11', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.63  thf(t83_xboole_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.63  thf('12', plain,
% 0.41/0.63      (![X15 : $i, X16 : $i]:
% 0.41/0.63         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.41/0.63      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.63  thf('13', plain,
% 0.41/0.63      (![X18 : $i, X19 : $i]:
% 0.41/0.63         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.41/0.63  thf('14', plain,
% 0.41/0.63      (![X15 : $i, X16 : $i]:
% 0.41/0.63         (((k6_subset_1 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.41/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.63  thf('15', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X1 @ X0)) = (X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['11', '14'])).
% 0.41/0.63  thf(t38_xboole_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.41/0.63       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.63  thf('16', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i]:
% 0.41/0.63         (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.41/0.63      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.41/0.63  thf('17', plain,
% 0.41/0.63      (![X18 : $i, X19 : $i]:
% 0.41/0.63         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.41/0.63  thf('18', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i]:
% 0.41/0.63         (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ (k6_subset_1 @ X8 @ X7)))),
% 0.41/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.63  thf('19', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X0)
% 0.41/0.63          | ((k6_subset_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['15', '18'])).
% 0.41/0.63  thf('20', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['6', '19'])).
% 0.41/0.63  thf(t81_xboole_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.41/0.63       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.41/0.63  thf('21', plain,
% 0.41/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.63         ((r1_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.41/0.63          | ~ (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X12 @ X14)))),
% 0.41/0.63      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.41/0.63  thf('22', plain,
% 0.41/0.63      (![X18 : $i, X19 : $i]:
% 0.41/0.63         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.41/0.63  thf('23', plain,
% 0.41/0.63      (![X18 : $i, X19 : $i]:
% 0.41/0.63         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.41/0.63  thf('24', plain,
% 0.41/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.63         ((r1_xboole_0 @ X12 @ (k6_subset_1 @ X13 @ X14))
% 0.41/0.63          | ~ (r1_xboole_0 @ X13 @ (k6_subset_1 @ X12 @ X14)))),
% 0.41/0.63      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.41/0.63  thf('25', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.41/0.63          | (r1_xboole_0 @ sk_A @ (k6_subset_1 @ X0 @ sk_B)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['20', '24'])).
% 0.41/0.63  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.41/0.63  thf('26', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.41/0.63      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.41/0.63  thf('27', plain,
% 0.41/0.63      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k6_subset_1 @ X0 @ sk_B))),
% 0.41/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.63  thf(t212_relat_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ B ) =>
% 0.41/0.63       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.41/0.63         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.63  thf('28', plain,
% 0.41/0.63      (![X24 : $i, X25 : $i]:
% 0.41/0.63         (((k1_relat_1 @ (k6_subset_1 @ X24 @ (k7_relat_1 @ X24 @ X25)))
% 0.41/0.63            = (k6_subset_1 @ (k1_relat_1 @ X24) @ X25))
% 0.41/0.63          | ~ (v1_relat_1 @ X24))),
% 0.41/0.63      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.41/0.63  thf(t187_relat_1, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ A ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.41/0.63           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.41/0.63  thf('29', plain,
% 0.41/0.63      (![X22 : $i, X23 : $i]:
% 0.41/0.63         (~ (r1_xboole_0 @ X22 @ (k1_relat_1 @ X23))
% 0.41/0.63          | ((k7_relat_1 @ X23 @ X22) = (k1_xboole_0))
% 0.41/0.63          | ~ (v1_relat_1 @ X23))),
% 0.41/0.63      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.41/0.63  thf('30', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         (~ (r1_xboole_0 @ X2 @ (k6_subset_1 @ (k1_relat_1 @ X1) @ X0))
% 0.41/0.63          | ~ (v1_relat_1 @ X1)
% 0.41/0.63          | ~ (v1_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.41/0.63          | ((k7_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.41/0.63              = (k1_xboole_0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.63  thf('31', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.41/0.63            = (k1_xboole_0))
% 0.41/0.63          | ~ (v1_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)))
% 0.41/0.63          | ~ (v1_relat_1 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['27', '30'])).
% 0.41/0.63  thf(fc2_relat_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.41/0.63  thf('32', plain,
% 0.41/0.63      (![X20 : $i, X21 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k4_xboole_0 @ X20 @ X21)))),
% 0.41/0.63      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.41/0.63  thf('33', plain,
% 0.41/0.63      (![X18 : $i, X19 : $i]:
% 0.41/0.63         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.41/0.63  thf('34', plain,
% 0.41/0.63      (![X20 : $i, X21 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k6_subset_1 @ X20 @ X21)))),
% 0.41/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.41/0.63  thf('35', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X0)
% 0.41/0.63          | ((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.41/0.63              = (k1_xboole_0)))),
% 0.41/0.63      inference('clc', [status(thm)], ['31', '34'])).
% 0.41/0.63  thf('36', plain,
% 0.41/0.63      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.41/0.63         != (k1_xboole_0))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('37', plain,
% 0.41/0.63      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.41/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.63  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('39', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.41/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.63  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
