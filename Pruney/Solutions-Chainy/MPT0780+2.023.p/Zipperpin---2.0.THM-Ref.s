%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J6sVVjt2oq

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  368 ( 455 expanded)
%              Number of equality atoms :   35 (  44 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X53 @ X55 ) @ X54 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X53 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X50 @ X51 ) @ X52 )
        = ( k2_wellord1 @ X50 @ ( k3_xboole_0 @ X51 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X50 @ X51 ) @ X52 )
        = ( k2_wellord1 @ X50 @ ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('6',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('10',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ( ( k7_relat_1 @ X44 @ X45 )
        = X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,
    ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['7','26','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J6sVVjt2oq
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:12:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 109 iterations in 0.049s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(t27_wellord1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.20/0.51         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k2_wellord1 @ X53 @ X55) @ X54)
% 0.20/0.51            = (k2_wellord1 @ (k2_wellord1 @ X53 @ X54) @ X55))
% 0.20/0.51          | ~ (v1_relat_1 @ X53))),
% 0.20/0.51      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.20/0.51  thf(t26_wellord1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.20/0.51         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k2_wellord1 @ X50 @ X51) @ X52)
% 0.20/0.51            = (k2_wellord1 @ X50 @ (k3_xboole_0 @ X51 @ X52)))
% 0.20/0.51          | ~ (v1_relat_1 @ X50))),
% 0.20/0.51      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.20/0.51  thf(t12_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X35 : $i, X36 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k2_wellord1 @ X50 @ X51) @ X52)
% 0.20/0.51            = (k2_wellord1 @ X50 @ (k1_setfam_1 @ (k2_tarski @ X51 @ X52))))
% 0.20/0.51          | ~ (v1_relat_1 @ X50))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.20/0.51            = (k2_wellord1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))
% 0.20/0.51          | ~ (v1_relat_1 @ X2)
% 0.20/0.51          | ~ (v1_relat_1 @ X2))),
% 0.20/0.51      inference('sup+', [status(thm)], ['0', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X2)
% 0.20/0.51          | ((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.20/0.51              = (k2_wellord1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.51  thf(t29_wellord1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.51         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.20/0.51           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( v1_relat_1 @ C ) =>
% 0.20/0.51          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.51            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.20/0.51              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.20/0.51         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((((k2_wellord1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.20/0.51          != (k2_wellord1 @ sk_C @ sk_A))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t71_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.51  thf('9', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.20/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.51  thf(t97_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.51         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X44 : $i, X45 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 0.20/0.51          | ((k7_relat_1 @ X44 @ X45) = (X44))
% 0.20/0.51          | ~ (v1_relat_1 @ X44))),
% 0.20/0.51      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.51          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.51  thf('12', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(t94_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X42 : $i, X43 : $i]:
% 0.20/0.51         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.20/0.51          | ~ (v1_relat_1 @ X43))),
% 0.20/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.51  thf(t43_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.51       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X46 : $i, X47 : $i]:
% 0.20/0.51         ((k5_relat_1 @ (k6_relat_1 @ X47) @ (k6_relat_1 @ X46))
% 0.20/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X46 @ X47)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X35 : $i, X36 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X46 : $i, X47 : $i]:
% 0.20/0.51         ((k5_relat_1 @ (k6_relat_1 @ X47) @ (k6_relat_1 @ X46))
% 0.20/0.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X46 @ X47))))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.51            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.20/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['14', '17'])).
% 0.20/0.51  thf('19', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.20/0.51              = (k6_relat_1 @ X0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.20/0.51         = (k6_relat_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '21'])).
% 0.20/0.51  thf('23', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.20/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.20/0.51         = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.20/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.51  thf('26', plain, (((sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '26', '27'])).
% 0.20/0.51  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
