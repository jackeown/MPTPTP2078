%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I1K5SqFo22

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:03 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  63 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  439 ( 587 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X33 @ ( k7_relat_1 @ X33 @ X34 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X33 @ ( k7_relat_1 @ X33 @ X34 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) ) @ ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ X39 @ ( k1_relat_1 @ X40 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X40 @ X39 ) )
        = X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
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

thf('19',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I1K5SqFo22
% 0.15/0.37  % Computer   : n025.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:05:06 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 44 iterations in 0.044s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(t212_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.23/0.51         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (![X33 : $i, X34 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k6_subset_1 @ X33 @ (k7_relat_1 @ X33 @ X34)))
% 0.23/0.51            = (k6_subset_1 @ (k1_relat_1 @ X33) @ X34))
% 0.23/0.51          | ~ (v1_relat_1 @ X33))),
% 0.23/0.51      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.23/0.51  thf(redefinition_k6_subset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X29 : $i, X30 : $i]:
% 0.23/0.51         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X29 : $i, X30 : $i]:
% 0.23/0.51         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (![X33 : $i, X34 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k4_xboole_0 @ X33 @ (k7_relat_1 @ X33 @ X34)))
% 0.23/0.51            = (k4_xboole_0 @ (k1_relat_1 @ X33) @ X34))
% 0.23/0.51          | ~ (v1_relat_1 @ X33))),
% 0.23/0.51      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.23/0.51  thf(t90_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.23/0.51         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X37 : $i, X38 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.23/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X37) @ X38))
% 0.23/0.51          | ~ (v1_relat_1 @ X37))),
% 0.23/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X37 : $i, X38 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.23/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X37) @ X38))
% 0.23/0.51          | ~ (v1_relat_1 @ X37))),
% 0.23/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.23/0.51  thf(t89_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( r1_tarski @
% 0.23/0.51         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X35 : $i, X36 : $i]:
% 0.23/0.51         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X35 @ X36)) @ 
% 0.23/0.51           (k1_relat_1 @ X35))
% 0.23/0.51          | ~ (v1_relat_1 @ X35))),
% 0.23/0.51      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ 
% 0.23/0.51           (k1_relat_1 @ X1))
% 0.23/0.51          | ~ (v1_relat_1 @ X1)
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X1)
% 0.23/0.51          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ 
% 0.23/0.51             (k1_relat_1 @ X1)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.51  thf(t91_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.23/0.51         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X39 : $i, X40 : $i]:
% 0.23/0.51         (~ (r1_tarski @ X39 @ (k1_relat_1 @ X40))
% 0.23/0.51          | ((k1_relat_1 @ (k7_relat_1 @ X40 @ X39)) = (X39))
% 0.23/0.51          | ~ (v1_relat_1 @ X40))),
% 0.23/0.51      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X0)
% 0.23/0.51          | ((k1_relat_1 @ 
% 0.23/0.51              (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.23/0.51              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k1_relat_1 @ 
% 0.23/0.51            (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.23/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.23/0.51            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.23/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ X1)
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('sup+', [status(thm)], ['4', '11'])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X1)
% 0.23/0.51          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.23/0.51              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.23/0.51              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.51  thf(t100_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X0 @ X1)
% 0.23/0.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.23/0.51            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.23/0.51            = (k5_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.23/0.51               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X0 @ X1)
% 0.23/0.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.23/0.51            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.23/0.51            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X37 : $i, X38 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.23/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X37) @ X38))
% 0.23/0.51          | ~ (v1_relat_1 @ X37))),
% 0.23/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.23/0.51  thf(t213_relat_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( k6_subset_1 @
% 0.23/0.51           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.23/0.51         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i]:
% 0.23/0.51        ( ( v1_relat_1 @ B ) =>
% 0.23/0.51          ( ( k6_subset_1 @
% 0.23/0.51              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.23/0.51            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.23/0.51         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.23/0.51         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X29 : $i, X30 : $i]:
% 0.23/0.51         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X29 : $i, X30 : $i]:
% 0.23/0.51         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.23/0.51         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.23/0.51         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.23/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.23/0.51          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.23/0.51          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.23/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['18', '22'])).
% 0.23/0.51  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.23/0.51         (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.23/0.51         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.23/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.23/0.51          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.23/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['17', '25'])).
% 0.23/0.51  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('28', plain,
% 0.23/0.51      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.23/0.51         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.23/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.23/0.51  thf('29', plain,
% 0.23/0.51      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.23/0.51          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.23/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '28'])).
% 0.23/0.51  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.23/0.51         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.23/0.51  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
