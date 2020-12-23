%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LocX32iEXw

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   56 (  80 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  401 ( 652 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X3 )
        = ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

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

thf('2',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ( ( k7_relat_1 @ X8 @ X9 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X3 )
        = ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('26',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LocX32iEXw
% 0.17/0.37  % Computer   : n013.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 19:02:55 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 21 iterations in 0.025s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.51  thf(t94_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i]:
% 0.23/0.51         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 0.23/0.51          | ~ (v1_relat_1 @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.23/0.51  thf(t181_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ![C:$i]:
% 0.23/0.51         ( ( v1_relat_1 @ C ) =>
% 0.23/0.51           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.23/0.51             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X1)
% 0.23/0.51          | ((k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X3)
% 0.23/0.51              = (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X3)))
% 0.23/0.51          | ~ (v1_relat_1 @ X2))),
% 0.23/0.51      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.23/0.51  thf(t175_funct_2, conjecture,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.51       ( ![B:$i,C:$i]:
% 0.23/0.51         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.23/0.51           ( ( k10_relat_1 @ A @ C ) =
% 0.23/0.51             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]:
% 0.23/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.51          ( ![B:$i,C:$i]:
% 0.23/0.51            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.23/0.51              ( ( k10_relat_1 @ A @ C ) =
% 0.23/0.51                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.23/0.51  thf('2', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t71_relat_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.23/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.51  thf('3', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.51  thf(t97_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.23/0.51         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i]:
% 0.23/0.51         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.23/0.51          | ((k7_relat_1 @ X8 @ X9) = (X8))
% 0.23/0.51          | ~ (v1_relat_1 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.23/0.51          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(fc3_funct_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.23/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.23/0.51  thf('6', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.51          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.23/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (((k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)
% 0.23/0.51         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['2', '7'])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i]:
% 0.23/0.51         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 0.23/0.51          | ~ (v1_relat_1 @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.23/0.51  thf('10', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.23/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.51  thf(t169_relat_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.23/0.51            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.23/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.23/0.51  thf('13', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.51  thf('14', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X1)
% 0.23/0.51          | ((k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X3)
% 0.23/0.51              = (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X3)))
% 0.23/0.51          | ~ (v1_relat_1 @ X2))),
% 0.23/0.51      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.23/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ X1)
% 0.23/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('18', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.23/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.23/0.51            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.23/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.23/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['9', '19'])).
% 0.23/0.51  thf('21', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.51  thf('22', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.23/0.51           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.23/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.23/0.51         (k10_relat_1 @ sk_A @ sk_C))
% 0.23/0.51         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['8', '23'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (((k10_relat_1 @ sk_A @ sk_C)
% 0.23/0.51         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.23/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.51  thf('27', plain,
% 0.23/0.51      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.23/0.51          = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C))
% 0.23/0.51        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.23/0.51        | ~ (v1_relat_1 @ sk_A))),
% 0.23/0.51      inference('sup+', [status(thm)], ['1', '26'])).
% 0.23/0.51  thf('28', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.51  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('30', plain,
% 0.23/0.51      (((k10_relat_1 @ sk_A @ sk_C)
% 0.23/0.51         = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C))),
% 0.23/0.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.23/0.51          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.23/0.51        | ~ (v1_relat_1 @ sk_A))),
% 0.23/0.51      inference('sup+', [status(thm)], ['0', '30'])).
% 0.23/0.51  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('33', plain,
% 0.23/0.51      (((k10_relat_1 @ sk_A @ sk_C)
% 0.23/0.51         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.23/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.23/0.51  thf('34', plain,
% 0.23/0.51      (((k10_relat_1 @ sk_A @ sk_C)
% 0.23/0.51         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('35', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
