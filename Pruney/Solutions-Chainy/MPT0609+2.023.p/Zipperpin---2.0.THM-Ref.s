%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZFXhojZ2nQ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:01 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   49 (  65 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  419 ( 584 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ( ( k6_subset_1 @ X44 @ ( k7_relat_1 @ X44 @ X46 ) )
        = ( k7_relat_1 @ X44 @ ( k6_subset_1 @ X45 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ( ( k4_xboole_0 @ X44 @ ( k7_relat_1 @ X44 @ X46 ) )
        = ( k7_relat_1 @ X44 @ ( k4_xboole_0 @ X45 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X49 ) @ X50 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X49 ) @ X50 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X49 ) @ X50 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('19',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZFXhojZ2nQ
% 0.13/0.36  % Computer   : n020.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 09:59:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.00/1.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.23  % Solved by: fo/fo7.sh
% 1.00/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.23  % done 809 iterations in 0.756s
% 1.00/1.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.23  % SZS output start Refutation
% 1.00/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.23  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.00/1.23  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.00/1.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.00/1.23  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.00/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.00/1.23  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.00/1.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.00/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.23  thf(d10_xboole_0, axiom,
% 1.00/1.23    (![A:$i,B:$i]:
% 1.00/1.23     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.00/1.23  thf('0', plain,
% 1.00/1.23      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.00/1.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.00/1.23  thf('1', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.00/1.23      inference('simplify', [status(thm)], ['0'])).
% 1.00/1.23  thf(t211_relat_1, axiom,
% 1.00/1.23    (![A:$i,B:$i,C:$i]:
% 1.00/1.23     ( ( v1_relat_1 @ C ) =>
% 1.00/1.23       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 1.00/1.23         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 1.00/1.23           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 1.00/1.23  thf('2', plain,
% 1.00/1.23      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.00/1.23         (~ (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 1.00/1.23          | ((k6_subset_1 @ X44 @ (k7_relat_1 @ X44 @ X46))
% 1.00/1.23              = (k7_relat_1 @ X44 @ (k6_subset_1 @ X45 @ X46)))
% 1.00/1.23          | ~ (v1_relat_1 @ X44))),
% 1.00/1.23      inference('cnf', [status(esa)], [t211_relat_1])).
% 1.00/1.23  thf(redefinition_k6_subset_1, axiom,
% 1.00/1.23    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.00/1.23  thf('3', plain,
% 1.00/1.23      (![X37 : $i, X38 : $i]:
% 1.00/1.23         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 1.00/1.23      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.00/1.23  thf('4', plain,
% 1.00/1.23      (![X37 : $i, X38 : $i]:
% 1.00/1.23         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 1.00/1.23      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.00/1.23  thf('5', plain,
% 1.00/1.23      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.00/1.23         (~ (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 1.00/1.23          | ((k4_xboole_0 @ X44 @ (k7_relat_1 @ X44 @ X46))
% 1.00/1.23              = (k7_relat_1 @ X44 @ (k4_xboole_0 @ X45 @ X46)))
% 1.00/1.23          | ~ (v1_relat_1 @ X44))),
% 1.00/1.23      inference('demod', [status(thm)], ['2', '3', '4'])).
% 1.00/1.23  thf('6', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         (~ (v1_relat_1 @ X0)
% 1.00/1.23          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 1.00/1.23              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 1.00/1.23      inference('sup-', [status(thm)], ['1', '5'])).
% 1.00/1.23  thf(t90_relat_1, axiom,
% 1.00/1.23    (![A:$i,B:$i]:
% 1.00/1.23     ( ( v1_relat_1 @ B ) =>
% 1.00/1.23       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.00/1.23         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.00/1.23  thf('7', plain,
% 1.00/1.23      (![X49 : $i, X50 : $i]:
% 1.00/1.23         (((k1_relat_1 @ (k7_relat_1 @ X49 @ X50))
% 1.00/1.23            = (k3_xboole_0 @ (k1_relat_1 @ X49) @ X50))
% 1.00/1.23          | ~ (v1_relat_1 @ X49))),
% 1.00/1.23      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.00/1.23  thf(t12_setfam_1, axiom,
% 1.00/1.23    (![A:$i,B:$i]:
% 1.00/1.23     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.00/1.23  thf('8', plain,
% 1.00/1.23      (![X39 : $i, X40 : $i]:
% 1.00/1.23         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.00/1.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.00/1.23  thf('9', plain,
% 1.00/1.23      (![X49 : $i, X50 : $i]:
% 1.00/1.23         (((k1_relat_1 @ (k7_relat_1 @ X49 @ X50))
% 1.00/1.23            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X49) @ X50)))
% 1.00/1.23          | ~ (v1_relat_1 @ X49))),
% 1.00/1.23      inference('demod', [status(thm)], ['7', '8'])).
% 1.00/1.23  thf('10', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 1.00/1.23            = (k1_setfam_1 @ 
% 1.00/1.23               (k2_tarski @ (k1_relat_1 @ X1) @ 
% 1.00/1.23                (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))))
% 1.00/1.23          | ~ (v1_relat_1 @ X1)
% 1.00/1.23          | ~ (v1_relat_1 @ X1))),
% 1.00/1.23      inference('sup+', [status(thm)], ['6', '9'])).
% 1.00/1.23  thf(t48_xboole_1, axiom,
% 1.00/1.23    (![A:$i,B:$i]:
% 1.00/1.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.00/1.23  thf('11', plain,
% 1.00/1.23      (![X8 : $i, X9 : $i]:
% 1.00/1.23         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.23           = (k3_xboole_0 @ X8 @ X9))),
% 1.00/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.23  thf('12', plain,
% 1.00/1.23      (![X39 : $i, X40 : $i]:
% 1.00/1.23         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.00/1.23      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.00/1.23  thf('13', plain,
% 1.00/1.23      (![X8 : $i, X9 : $i]:
% 1.00/1.23         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.23           = (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))),
% 1.00/1.23      inference('demod', [status(thm)], ['11', '12'])).
% 1.00/1.23  thf('14', plain,
% 1.00/1.23      (![X8 : $i, X9 : $i]:
% 1.00/1.23         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.23           = (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))),
% 1.00/1.23      inference('demod', [status(thm)], ['11', '12'])).
% 1.00/1.23  thf('15', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.00/1.23           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.00/1.23      inference('sup+', [status(thm)], ['13', '14'])).
% 1.00/1.23  thf('16', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 1.00/1.23            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.00/1.23               (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X1) @ X0))))
% 1.00/1.23          | ~ (v1_relat_1 @ X1)
% 1.00/1.23          | ~ (v1_relat_1 @ X1))),
% 1.00/1.23      inference('demod', [status(thm)], ['10', '15'])).
% 1.00/1.23  thf('17', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         (~ (v1_relat_1 @ X1)
% 1.00/1.23          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 1.00/1.23              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.00/1.23                 (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X1) @ X0)))))),
% 1.00/1.23      inference('simplify', [status(thm)], ['16'])).
% 1.00/1.23  thf('18', plain,
% 1.00/1.23      (![X49 : $i, X50 : $i]:
% 1.00/1.23         (((k1_relat_1 @ (k7_relat_1 @ X49 @ X50))
% 1.00/1.23            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X49) @ X50)))
% 1.00/1.23          | ~ (v1_relat_1 @ X49))),
% 1.00/1.23      inference('demod', [status(thm)], ['7', '8'])).
% 1.00/1.23  thf(t213_relat_1, conjecture,
% 1.00/1.23    (![A:$i,B:$i]:
% 1.00/1.23     ( ( v1_relat_1 @ B ) =>
% 1.00/1.23       ( ( k6_subset_1 @
% 1.00/1.23           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 1.00/1.23         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 1.00/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.23    (~( ![A:$i,B:$i]:
% 1.00/1.23        ( ( v1_relat_1 @ B ) =>
% 1.00/1.23          ( ( k6_subset_1 @
% 1.00/1.23              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 1.00/1.23            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 1.00/1.23    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 1.00/1.23  thf('19', plain,
% 1.00/1.23      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 1.00/1.23         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.00/1.23         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.23  thf('20', plain,
% 1.00/1.23      (![X37 : $i, X38 : $i]:
% 1.00/1.23         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 1.00/1.23      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.00/1.23  thf('21', plain,
% 1.00/1.23      (![X37 : $i, X38 : $i]:
% 1.00/1.23         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 1.00/1.23      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.00/1.23  thf('22', plain,
% 1.00/1.23      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 1.00/1.23         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.00/1.23         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.23      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.00/1.23  thf('23', plain,
% 1.00/1.23      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 1.00/1.23          (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.00/1.23          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 1.00/1.23        | ~ (v1_relat_1 @ sk_B))),
% 1.00/1.23      inference('sup-', [status(thm)], ['18', '22'])).
% 1.00/1.23  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.23  thf('25', plain,
% 1.00/1.23      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 1.00/1.23         (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.00/1.23         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.23      inference('demod', [status(thm)], ['23', '24'])).
% 1.00/1.23  thf('26', plain,
% 1.00/1.23      ((((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.00/1.23          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 1.00/1.23        | ~ (v1_relat_1 @ sk_B))),
% 1.00/1.23      inference('sup-', [status(thm)], ['17', '25'])).
% 1.00/1.23  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.23  thf('28', plain,
% 1.00/1.23      (((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.00/1.23         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.23      inference('demod', [status(thm)], ['26', '27'])).
% 1.00/1.23  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 1.00/1.23  
% 1.00/1.23  % SZS output end Refutation
% 1.00/1.23  
% 1.07/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
