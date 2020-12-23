%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rcRYqvnZAw

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:00 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   64 (  79 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  554 ( 719 expanded)
%              Number of equality atoms :   46 (  61 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( ( k6_subset_1 @ X17 @ ( k7_relat_1 @ X17 @ X19 ) )
        = ( k7_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( ( k4_xboole_0 @ X17 @ ( k7_relat_1 @ X17 @ X19 ) )
        = ( k7_relat_1 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X15 @ ( k6_subset_1 @ ( k1_relat_1 @ X15 ) @ X16 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t191_relat_1])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X15 @ ( k4_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('28',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('31',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rcRYqvnZAw
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:53:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 183 iterations in 0.299s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.75  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.54/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.54/0.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(d10_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.54/0.75      inference('simplify', [status(thm)], ['0'])).
% 0.54/0.75  thf(t211_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ C ) =>
% 0.54/0.75       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.54/0.75         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.54/0.75           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.54/0.75          | ((k6_subset_1 @ X17 @ (k7_relat_1 @ X17 @ X19))
% 0.54/0.75              = (k7_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19)))
% 0.54/0.75          | ~ (v1_relat_1 @ X17))),
% 0.54/0.75      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.54/0.75  thf(redefinition_k6_subset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]:
% 0.54/0.75         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.54/0.75  thf('4', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]:
% 0.54/0.75         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.54/0.75          | ((k4_xboole_0 @ X17 @ (k7_relat_1 @ X17 @ X19))
% 0.54/0.75              = (k7_relat_1 @ X17 @ (k4_xboole_0 @ X18 @ X19)))
% 0.54/0.75          | ~ (v1_relat_1 @ X17))),
% 0.54/0.75      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.54/0.75              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '5'])).
% 0.54/0.75  thf(t191_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( k1_relat_1 @
% 0.54/0.75           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.54/0.75         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         (((k1_relat_1 @ 
% 0.54/0.75            (k7_relat_1 @ X15 @ (k6_subset_1 @ (k1_relat_1 @ X15) @ X16)))
% 0.54/0.75            = (k6_subset_1 @ (k1_relat_1 @ X15) @ X16))
% 0.54/0.75          | ~ (v1_relat_1 @ X15))),
% 0.54/0.75      inference('cnf', [status(esa)], [t191_relat_1])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]:
% 0.54/0.75         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]:
% 0.54/0.75         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         (((k1_relat_1 @ 
% 0.54/0.75            (k7_relat_1 @ X15 @ (k4_xboole_0 @ (k1_relat_1 @ X15) @ X16)))
% 0.54/0.75            = (k4_xboole_0 @ (k1_relat_1 @ X15) @ X16))
% 0.54/0.75          | ~ (v1_relat_1 @ X15))),
% 0.54/0.75      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.54/0.75            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X1)
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['6', '10'])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X1)
% 0.54/0.75          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.54/0.75              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['11'])).
% 0.54/0.75  thf(t90_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.54/0.75         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 0.54/0.75            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 0.54/0.75          | ~ (v1_relat_1 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.54/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf(t17_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.54/0.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.54/0.75      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.75  thf(t91_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.54/0.75         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i]:
% 0.54/0.75         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 0.54/0.75          | ((k1_relat_1 @ (k7_relat_1 @ X23 @ X22)) = (X22))
% 0.54/0.75          | ~ (v1_relat_1 @ X23))),
% 0.54/0.75      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k1_relat_1 @ 
% 0.54/0.75              (k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.54/0.75              = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k3_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.54/0.75            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.54/0.75            = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['13', '18'])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.54/0.75              (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.54/0.75              = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['19'])).
% 0.54/0.75  thf(t100_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X5 : $i, X6 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X5 @ X6)
% 0.54/0.75           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.54/0.75            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.54/0.75            = (k5_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.54/0.75               (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.54/0.75          | ~ (v1_relat_1 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['20', '21'])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (![X5 : $i, X6 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X5 @ X6)
% 0.54/0.75           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['23', '24'])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.54/0.75            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.54/0.75            = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.54/0.75          | ~ (v1_relat_1 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['22', '25'])).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 0.54/0.75            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 0.54/0.75          | ~ (v1_relat_1 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.54/0.75  thf(t213_relat_1, conjecture,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( k6_subset_1 @
% 0.54/0.75           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.54/0.75         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i]:
% 0.54/0.75        ( ( v1_relat_1 @ B ) =>
% 0.54/0.75          ( ( k6_subset_1 @
% 0.54/0.75              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.54/0.75            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.54/0.75         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.54/0.75         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]:
% 0.54/0.75         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]:
% 0.54/0.75         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.54/0.75         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.54/0.75         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.54/0.75      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.54/0.75          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.54/0.75          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['27', '31'])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.54/0.75         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.54/0.75         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.54/0.75      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.75          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['26', '35'])).
% 0.54/0.75  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.75         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.54/0.75      inference('demod', [status(thm)], ['36', '37'])).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.75          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['12', '38'])).
% 0.54/0.75  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.75         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['39', '40'])).
% 0.54/0.75  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
