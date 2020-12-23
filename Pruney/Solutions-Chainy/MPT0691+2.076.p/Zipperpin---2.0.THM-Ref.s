%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KvOtDurnfn

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:28 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   64 (  76 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  474 ( 596 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
        = ( k9_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( ( k10_relat_1 @ X4 @ ( k2_relat_1 @ X4 ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['17','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KvOtDurnfn
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:38:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 95 iterations in 0.089s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.56  thf(t146_funct_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.56         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( v1_relat_1 @ B ) =>
% 0.38/0.56          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.56            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t91_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.56         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.38/0.56          | ((k1_relat_1 @ (k7_relat_1 @ X15 @ X14)) = (X14))
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.56        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('5', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.56  thf(t148_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X2 : $i, X3 : $i]:
% 0.38/0.56         (((k2_relat_1 @ (k7_relat_1 @ X2 @ X3)) = (k9_relat_1 @ X2 @ X3))
% 0.38/0.56          | ~ (v1_relat_1 @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.56  thf(t169_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X4 : $i]:
% 0.38/0.56         (((k10_relat_1 @ X4 @ (k2_relat_1 @ X4)) = (k1_relat_1 @ X4))
% 0.38/0.56          | ~ (v1_relat_1 @ X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.38/0.56            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.56  thf(dt_k7_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X1)
% 0.38/0.56          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.38/0.56              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.38/0.56      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf(t94_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i]:
% 0.38/0.56         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 0.38/0.56          | ~ (v1_relat_1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.38/0.56  thf(t181_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( v1_relat_1 @ C ) =>
% 0.38/0.56           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.38/0.56             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X5)
% 0.38/0.56          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.38/0.56              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 0.38/0.56          | ~ (v1_relat_1 @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.38/0.56  thf(t71_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.56  thf('13', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.38/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.56  thf(t89_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( r1_tarski @
% 0.38/0.56         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i]:
% 0.38/0.56         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X12 @ X13)) @ 
% 0.38/0.56           (k1_relat_1 @ X12))
% 0.38/0.56          | ~ (v1_relat_1 @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.38/0.56           X0)
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['13', '14'])).
% 0.38/0.56  thf(fc3_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.56  thf('16', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0)),
% 0.38/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i]:
% 0.38/0.56         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 0.38/0.56          | ~ (v1_relat_1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.38/0.56  thf('19', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.38/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.56  thf(t182_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( v1_relat_1 @ B ) =>
% 0.38/0.56           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.38/0.56             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X8)
% 0.38/0.56          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.38/0.56              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.38/0.56          | ~ (v1_relat_1 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.38/0.56            = (k10_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.56  thf('22', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.38/0.56            = (k10_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.38/0.56            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['18', '23'])).
% 0.38/0.56  thf('25', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.56  thf('26', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.38/0.56           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 0.38/0.56      inference('demod', [status(thm)], ['17', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_tarski @ 
% 0.38/0.56           (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 0.38/0.56           (k10_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['12', '28'])).
% 0.38/0.56  thf('30', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_tarski @ 
% 0.38/0.56           (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 0.38/0.56           (k10_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.38/0.56           (k10_relat_1 @ X1 @ X2))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['11', '31'])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.38/0.56             (k10_relat_1 @ X1 @ X2)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.38/0.56           (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['10', '33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.38/0.56             (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.38/0.56        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['5', '35'])).
% 0.38/0.56  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.56  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
