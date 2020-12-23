%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wPxY5tblLm

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:59 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   63 (  78 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  504 ( 648 expanded)
%              Number of equality atoms :   44 (  59 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X45 ) @ X46 )
      | ( ( k6_subset_1 @ X45 @ ( k7_relat_1 @ X45 @ X47 ) )
        = ( k7_relat_1 @ X45 @ ( k6_subset_1 @ X46 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X45 ) @ X46 )
      | ( ( k4_xboole_0 @ X45 @ ( k7_relat_1 @ X45 @ X47 ) )
        = ( k7_relat_1 @ X45 @ ( k4_xboole_0 @ X46 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t191_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X43 @ ( k6_subset_1 @ ( k1_relat_1 @ X43 ) @ X44 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X43 ) @ X44 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t191_relat_1])).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X43 @ ( k4_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X48 @ X49 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X48 ) @ X49 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t213_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
        = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
          = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t213_relat_1])).

thf('14',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ ( k3_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wPxY5tblLm
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:22:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.17  % Solved by: fo/fo7.sh
% 0.91/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.17  % done 891 iterations in 0.716s
% 0.91/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.17  % SZS output start Refutation
% 0.91/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.17  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.91/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.17  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.91/1.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.17  thf(d10_xboole_0, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.17  thf('0', plain,
% 0.91/1.17      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.91/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.17  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.91/1.17      inference('simplify', [status(thm)], ['0'])).
% 0.91/1.17  thf(t211_relat_1, axiom,
% 0.91/1.17    (![A:$i,B:$i,C:$i]:
% 0.91/1.17     ( ( v1_relat_1 @ C ) =>
% 0.91/1.17       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.91/1.17         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.91/1.17           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.91/1.17  thf('2', plain,
% 0.91/1.17      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.91/1.17         (~ (r1_tarski @ (k1_relat_1 @ X45) @ X46)
% 0.91/1.17          | ((k6_subset_1 @ X45 @ (k7_relat_1 @ X45 @ X47))
% 0.91/1.17              = (k7_relat_1 @ X45 @ (k6_subset_1 @ X46 @ X47)))
% 0.91/1.17          | ~ (v1_relat_1 @ X45))),
% 0.91/1.17      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.91/1.17  thf(redefinition_k6_subset_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.91/1.17  thf('3', plain,
% 0.91/1.17      (![X39 : $i, X40 : $i]:
% 0.91/1.17         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.17  thf('4', plain,
% 0.91/1.17      (![X39 : $i, X40 : $i]:
% 0.91/1.17         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.17  thf('5', plain,
% 0.91/1.17      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.91/1.17         (~ (r1_tarski @ (k1_relat_1 @ X45) @ X46)
% 0.91/1.17          | ((k4_xboole_0 @ X45 @ (k7_relat_1 @ X45 @ X47))
% 0.91/1.17              = (k7_relat_1 @ X45 @ (k4_xboole_0 @ X46 @ X47)))
% 0.91/1.17          | ~ (v1_relat_1 @ X45))),
% 0.91/1.17      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.91/1.17  thf('6', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         (~ (v1_relat_1 @ X0)
% 0.91/1.17          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.91/1.17              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.91/1.17      inference('sup-', [status(thm)], ['1', '5'])).
% 0.91/1.17  thf(t191_relat_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( v1_relat_1 @ B ) =>
% 0.91/1.17       ( ( k1_relat_1 @
% 0.91/1.17           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.91/1.17         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.17  thf('7', plain,
% 0.91/1.17      (![X43 : $i, X44 : $i]:
% 0.91/1.17         (((k1_relat_1 @ 
% 0.91/1.17            (k7_relat_1 @ X43 @ (k6_subset_1 @ (k1_relat_1 @ X43) @ X44)))
% 0.91/1.17            = (k6_subset_1 @ (k1_relat_1 @ X43) @ X44))
% 0.91/1.17          | ~ (v1_relat_1 @ X43))),
% 0.91/1.17      inference('cnf', [status(esa)], [t191_relat_1])).
% 0.91/1.17  thf('8', plain,
% 0.91/1.17      (![X39 : $i, X40 : $i]:
% 0.91/1.17         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.17  thf('9', plain,
% 0.91/1.17      (![X39 : $i, X40 : $i]:
% 0.91/1.17         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.17  thf('10', plain,
% 0.91/1.17      (![X43 : $i, X44 : $i]:
% 0.91/1.17         (((k1_relat_1 @ 
% 0.91/1.17            (k7_relat_1 @ X43 @ (k4_xboole_0 @ (k1_relat_1 @ X43) @ X44)))
% 0.91/1.17            = (k4_xboole_0 @ (k1_relat_1 @ X43) @ X44))
% 0.91/1.17          | ~ (v1_relat_1 @ X43))),
% 0.91/1.17      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.91/1.17  thf('11', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.91/1.17            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.91/1.17          | ~ (v1_relat_1 @ X1)
% 0.91/1.17          | ~ (v1_relat_1 @ X1))),
% 0.91/1.17      inference('sup+', [status(thm)], ['6', '10'])).
% 0.91/1.17  thf('12', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         (~ (v1_relat_1 @ X1)
% 0.91/1.17          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.91/1.17              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.91/1.17      inference('simplify', [status(thm)], ['11'])).
% 0.91/1.17  thf(t90_relat_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( v1_relat_1 @ B ) =>
% 0.91/1.17       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.91/1.17         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.17  thf('13', plain,
% 0.91/1.17      (![X48 : $i, X49 : $i]:
% 0.91/1.17         (((k1_relat_1 @ (k7_relat_1 @ X48 @ X49))
% 0.91/1.17            = (k3_xboole_0 @ (k1_relat_1 @ X48) @ X49))
% 0.91/1.17          | ~ (v1_relat_1 @ X48))),
% 0.91/1.17      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.91/1.17  thf(t213_relat_1, conjecture,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( v1_relat_1 @ B ) =>
% 0.91/1.17       ( ( k6_subset_1 @
% 0.91/1.17           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.91/1.17         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.91/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.17    (~( ![A:$i,B:$i]:
% 0.91/1.17        ( ( v1_relat_1 @ B ) =>
% 0.91/1.17          ( ( k6_subset_1 @
% 0.91/1.17              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.91/1.17            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.91/1.17    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.91/1.17  thf('14', plain,
% 0.91/1.17      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.91/1.17         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.91/1.17         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('15', plain,
% 0.91/1.17      (![X39 : $i, X40 : $i]:
% 0.91/1.17         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.17  thf('16', plain,
% 0.91/1.17      (![X39 : $i, X40 : $i]:
% 0.91/1.17         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.17  thf('17', plain,
% 0.91/1.17      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.91/1.17         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.91/1.17         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.91/1.18      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.91/1.18  thf('18', plain,
% 0.91/1.18      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.91/1.18          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.91/1.18          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.91/1.18        | ~ (v1_relat_1 @ sk_B))),
% 0.91/1.18      inference('sup-', [status(thm)], ['13', '17'])).
% 0.91/1.18  thf(commutativity_k3_xboole_0, axiom,
% 0.91/1.18    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.91/1.18  thf('19', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.18  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('21', plain,
% 0.91/1.18      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.91/1.18         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.91/1.18         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.91/1.18      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.91/1.18  thf('22', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.18  thf('23', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.91/1.18      inference('simplify', [status(thm)], ['0'])).
% 0.91/1.18  thf(t108_xboole_1, axiom,
% 0.91/1.18    (![A:$i,B:$i,C:$i]:
% 0.91/1.18     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.91/1.18  thf('24', plain,
% 0.91/1.18      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.18         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ (k3_xboole_0 @ X7 @ X9) @ X8))),
% 0.91/1.18      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.91/1.18  thf('25', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.91/1.18      inference('sup-', [status(thm)], ['23', '24'])).
% 0.91/1.18  thf('26', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.18      inference('sup+', [status(thm)], ['22', '25'])).
% 0.91/1.18  thf(t28_xboole_1, axiom,
% 0.91/1.18    (![A:$i,B:$i]:
% 0.91/1.18     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.18  thf('27', plain,
% 0.91/1.18      (![X10 : $i, X11 : $i]:
% 0.91/1.18         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.91/1.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.18  thf('28', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]:
% 0.91/1.18         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.91/1.18           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.18      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.18  thf('29', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.18  thf('30', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]:
% 0.91/1.18         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.18           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.18      inference('demod', [status(thm)], ['28', '29'])).
% 0.91/1.18  thf(t100_xboole_1, axiom,
% 0.91/1.18    (![A:$i,B:$i]:
% 0.91/1.18     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.18  thf('31', plain,
% 0.91/1.18      (![X5 : $i, X6 : $i]:
% 0.91/1.18         ((k4_xboole_0 @ X5 @ X6)
% 0.91/1.18           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.91/1.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.18  thf('32', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]:
% 0.91/1.18         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.18      inference('sup+', [status(thm)], ['30', '31'])).
% 0.91/1.18  thf('33', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.18  thf('34', plain,
% 0.91/1.18      (![X5 : $i, X6 : $i]:
% 0.91/1.18         ((k4_xboole_0 @ X5 @ X6)
% 0.91/1.18           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.91/1.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.18  thf('35', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]:
% 0.91/1.18         ((k4_xboole_0 @ X0 @ X1)
% 0.91/1.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.18      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.18  thf('36', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]:
% 0.91/1.18         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.18           = (k4_xboole_0 @ X0 @ X1))),
% 0.91/1.18      inference('demod', [status(thm)], ['32', '35'])).
% 0.91/1.18  thf('37', plain,
% 0.91/1.18      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.91/1.18         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.91/1.18      inference('demod', [status(thm)], ['21', '36'])).
% 0.91/1.18  thf('38', plain,
% 0.91/1.18      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.91/1.18          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.91/1.18        | ~ (v1_relat_1 @ sk_B))),
% 0.91/1.18      inference('sup-', [status(thm)], ['12', '37'])).
% 0.91/1.18  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('40', plain,
% 0.91/1.18      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.91/1.18         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.91/1.18      inference('demod', [status(thm)], ['38', '39'])).
% 0.91/1.18  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.91/1.18  
% 0.91/1.18  % SZS output end Refutation
% 0.91/1.18  
% 1.01/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
