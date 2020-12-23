%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.whgzjqdbXe

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  220 ( 254 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k7_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) )
        = ( k7_relat_1 @ X11 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ ( k1_relat_1 @ X11 ) ) ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t192_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k7_relat_1 @ B @ A )
          = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_relat_1])).

thf('9',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.whgzjqdbXe
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 25 iterations in 0.018s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.43  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.43  thf(t71_relat_1, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.43       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.43  thf('0', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.20/0.43      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.43  thf(t90_relat_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ B ) =>
% 0.20/0.43       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.20/0.43         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (![X14 : $i, X15 : $i]:
% 0.20/0.43         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.20/0.43            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.20/0.43          | ~ (v1_relat_1 @ X14))),
% 0.20/0.43      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.43  thf(t189_relat_1, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ A ) =>
% 0.20/0.43       ( ![B:$i]:
% 0.20/0.43         ( ( v1_relat_1 @ B ) =>
% 0.20/0.43           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.20/0.43             ( k7_relat_1 @
% 0.20/0.43               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X10 : $i, X11 : $i]:
% 0.20/0.43         (~ (v1_relat_1 @ X10)
% 0.20/0.43          | ((k7_relat_1 @ X11 @ (k1_relat_1 @ X10))
% 0.20/0.43              = (k7_relat_1 @ X11 @ 
% 0.20/0.43                 (k1_relat_1 @ (k7_relat_1 @ X10 @ (k1_relat_1 @ X11)))))
% 0.20/0.43          | ~ (v1_relat_1 @ X11))),
% 0.20/0.43      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X1))
% 0.20/0.43            = (k7_relat_1 @ X0 @ 
% 0.20/0.43               (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0))))
% 0.20/0.43          | ~ (v1_relat_1 @ X1)
% 0.20/0.43          | ~ (v1_relat_1 @ X0)
% 0.20/0.43          | ~ (v1_relat_1 @ X1))),
% 0.20/0.43      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         (~ (v1_relat_1 @ X0)
% 0.20/0.43          | ~ (v1_relat_1 @ X1)
% 0.20/0.43          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X1))
% 0.20/0.43              = (k7_relat_1 @ X0 @ 
% 0.20/0.43                 (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))))),
% 0.20/0.43      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         (((k7_relat_1 @ X1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.43            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))
% 0.20/0.43          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.43          | ~ (v1_relat_1 @ X1))),
% 0.20/0.43      inference('sup+', [status(thm)], ['0', '4'])).
% 0.20/0.43  thf('6', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.20/0.43      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.43  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.43  thf('7', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.20/0.43      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         (((k7_relat_1 @ X1 @ X0)
% 0.20/0.43            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))
% 0.20/0.43          | ~ (v1_relat_1 @ X1))),
% 0.20/0.43      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.43  thf(t192_relat_1, conjecture,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ B ) =>
% 0.20/0.43       ( ( k7_relat_1 @ B @ A ) =
% 0.20/0.43         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i]:
% 0.20/0.43        ( ( v1_relat_1 @ B ) =>
% 0.20/0.43          ( ( k7_relat_1 @ B @ A ) =
% 0.20/0.43            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      (((k7_relat_1 @ sk_B @ sk_A)
% 0.20/0.43         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.43  thf('10', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.43      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (((k7_relat_1 @ sk_B @ sk_A)
% 0.20/0.43         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.43      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.43  thf('12', plain,
% 0.20/0.43      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.43        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.43  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 0.20/0.43      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.43  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
