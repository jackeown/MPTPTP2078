%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l51NvaU26M

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:39 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  344 ( 447 expanded)
%              Number of equality atoms :   34 (  43 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X43 ) @ X44 )
      | ( ( k7_relat_1 @ X43 @ X44 )
        = X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k7_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X41 ) @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X50 ) @ ( k6_relat_1 @ X49 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,
    ( ( k6_relat_1 @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('24',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l51NvaU26M
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:58:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 82 iterations in 0.039s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(t175_funct_2, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.48       ( ![B:$i,C:$i]:
% 0.19/0.48         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.19/0.48           ( ( k10_relat_1 @ A @ C ) =
% 0.19/0.48             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.48          ( ![B:$i,C:$i]:
% 0.19/0.48            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.19/0.48              ( ( k10_relat_1 @ A @ C ) =
% 0.19/0.48                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.19/0.48  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t71_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.48  thf('1', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf(t97_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.48         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X43 : $i, X44 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k1_relat_1 @ X43) @ X44)
% 0.19/0.48          | ((k7_relat_1 @ X43 @ X44) = (X43))
% 0.19/0.48          | ~ (v1_relat_1 @ X43))),
% 0.19/0.48      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.48          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.19/0.48  thf('4', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.48          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(t94_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X41 : $i, X42 : $i]:
% 0.19/0.48         (((k7_relat_1 @ X42 @ X41) = (k5_relat_1 @ (k6_relat_1 @ X41) @ X42))
% 0.19/0.48          | ~ (v1_relat_1 @ X42))),
% 0.19/0.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.48  thf(t43_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.48       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X49 : $i, X50 : $i]:
% 0.19/0.48         ((k5_relat_1 @ (k6_relat_1 @ X50) @ (k6_relat_1 @ X49))
% 0.19/0.48           = (k6_relat_1 @ (k3_xboole_0 @ X49 @ X50)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.48            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('9', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.48           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.48          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) = (k6_relat_1 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['5', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (((k6_relat_1 @ (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.19/0.48         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '11'])).
% 0.19/0.48  thf(commutativity_k2_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i]: ((k2_tarski @ X4 @ X3) = (k2_tarski @ X3 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.48  thf(t12_setfam_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X32 : $i, X33 : $i]:
% 0.19/0.48         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X32 : $i, X33 : $i]:
% 0.19/0.48         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (((k6_relat_1 @ (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.48         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['12', '17'])).
% 0.19/0.48  thf('19', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (((k1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.48         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.48         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf(t139_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ C ) =>
% 0.19/0.48       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.19/0.48         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.19/0.48         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.19/0.48            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.19/0.48          | ~ (v1_relat_1 @ X47))),
% 0.19/0.48      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.48         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.48          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.48         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['22', '27'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
