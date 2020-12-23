%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZN2WkQIy10

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  71 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  512 ( 663 expanded)
%              Number of equality atoms :   41 (  54 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( ( k6_subset_1 @ X40 @ ( k7_relat_1 @ X40 @ X42 ) )
        = ( k7_relat_1 @ X40 @ ( k6_subset_1 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( ( k4_xboole_0 @ X40 @ ( k7_relat_1 @ X40 @ X42 ) )
        = ( k7_relat_1 @ X40 @ ( k4_xboole_0 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X38 @ ( k6_subset_1 @ ( k1_relat_1 @ X38 ) @ X39 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t191_relat_1])).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X38 @ ( k4_xboole_0 @ ( k1_relat_1 @ X38 ) @ X39 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X43 @ X44 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('15',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ X45 @ ( k1_relat_1 @ X46 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X45 ) )
        = X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X43 @ X44 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
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

thf('24',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZN2WkQIy10
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 58 iterations in 0.094s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(d10_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.55  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.55  thf(t211_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ C ) =>
% 0.21/0.55       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.21/0.55         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.21/0.55           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.21/0.55          | ((k6_subset_1 @ X40 @ (k7_relat_1 @ X40 @ X42))
% 0.21/0.55              = (k7_relat_1 @ X40 @ (k6_subset_1 @ X41 @ X42)))
% 0.21/0.55          | ~ (v1_relat_1 @ X40))),
% 0.21/0.55      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.21/0.55  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X34 : $i, X35 : $i]:
% 0.21/0.55         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X34 : $i, X35 : $i]:
% 0.21/0.55         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.21/0.55          | ((k4_xboole_0 @ X40 @ (k7_relat_1 @ X40 @ X42))
% 0.21/0.55              = (k7_relat_1 @ X40 @ (k4_xboole_0 @ X41 @ X42)))
% 0.21/0.55          | ~ (v1_relat_1 @ X40))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.21/0.55              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '5'])).
% 0.21/0.55  thf(t191_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k1_relat_1 @
% 0.21/0.55           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.21/0.55         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X38 : $i, X39 : $i]:
% 0.21/0.55         (((k1_relat_1 @ 
% 0.21/0.55            (k7_relat_1 @ X38 @ (k6_subset_1 @ (k1_relat_1 @ X38) @ X39)))
% 0.21/0.55            = (k6_subset_1 @ (k1_relat_1 @ X38) @ X39))
% 0.21/0.55          | ~ (v1_relat_1 @ X38))),
% 0.21/0.55      inference('cnf', [status(esa)], [t191_relat_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X34 : $i, X35 : $i]:
% 0.21/0.55         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X34 : $i, X35 : $i]:
% 0.21/0.55         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X38 : $i, X39 : $i]:
% 0.21/0.55         (((k1_relat_1 @ 
% 0.21/0.55            (k7_relat_1 @ X38 @ (k4_xboole_0 @ (k1_relat_1 @ X38) @ X39)))
% 0.21/0.55            = (k4_xboole_0 @ (k1_relat_1 @ X38) @ X39))
% 0.21/0.55          | ~ (v1_relat_1 @ X38))),
% 0.21/0.55      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['6', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.55  thf(t90_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.55         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X43 : $i, X44 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k7_relat_1 @ X43 @ X44))
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X43) @ X44))
% 0.21/0.55          | ~ (v1_relat_1 @ X43))),
% 0.21/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.55  thf(t17_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.55  thf(t91_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.55         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X45 : $i, X46 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X45 @ (k1_relat_1 @ X46))
% 0.21/0.55          | ((k1_relat_1 @ (k7_relat_1 @ X46 @ X45)) = (X45))
% 0.21/0.55          | ~ (v1_relat_1 @ X46))),
% 0.21/0.55      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((k1_relat_1 @ 
% 0.21/0.55              (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.21/0.55              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.21/0.55            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.21/0.55              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.55  thf(t100_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.55           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.21/0.55            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55            = (k5_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.21/0.55               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.55           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.21/0.55            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X43 : $i, X44 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k7_relat_1 @ X43 @ X44))
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X43) @ X44))
% 0.21/0.55          | ~ (v1_relat_1 @ X43))),
% 0.21/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.55  thf(t213_relat_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k6_subset_1 @
% 0.21/0.55           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.21/0.55         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( v1_relat_1 @ B ) =>
% 0.21/0.55          ( ( k6_subset_1 @
% 0.21/0.55              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.21/0.55            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.21/0.55         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X34 : $i, X35 : $i]:
% 0.21/0.55         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X34 : $i, X35 : $i]:
% 0.21/0.55         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.21/0.55         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.21/0.55          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.55          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '27'])).
% 0.21/0.55  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.21/0.55         (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.55         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.55          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '30'])).
% 0.21/0.55  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.55         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.55          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '33'])).
% 0.21/0.55  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.55         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.55  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
