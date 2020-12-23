%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NZ00OaMQSQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:18 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  339 ( 423 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X20: $i] :
      ( ( ( k10_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X24 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k10_relat_1 @ X22 @ X23 ) @ ( k10_relat_1 @ X21 @ X23 ) )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NZ00OaMQSQ
% 0.12/0.35  % Computer   : n009.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 10:33:26 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 209 iterations in 0.160s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.61  thf(t146_funct_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.61         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i]:
% 0.40/0.61        ( ( v1_relat_1 @ B ) =>
% 0.40/0.61          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.61            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(t91_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.61         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X26 : $i, X27 : $i]:
% 0.40/0.61         (~ (r1_tarski @ X26 @ (k1_relat_1 @ X27))
% 0.40/0.61          | ((k1_relat_1 @ (k7_relat_1 @ X27 @ X26)) = (X26))
% 0.40/0.61          | ~ (v1_relat_1 @ X27))),
% 0.40/0.61      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.61        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.61  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('5', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['3', '4'])).
% 0.40/0.61  thf(t148_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X18 : $i, X19 : $i]:
% 0.40/0.61         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.40/0.61          | ~ (v1_relat_1 @ X18))),
% 0.40/0.61      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.40/0.61  thf(t169_relat_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ A ) =>
% 0.40/0.61       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X20 : $i]:
% 0.40/0.61         (((k10_relat_1 @ X20 @ (k2_relat_1 @ X20)) = (k1_relat_1 @ X20))
% 0.40/0.61          | ~ (v1_relat_1 @ X20))),
% 0.40/0.61      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.40/0.61            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.40/0.61          | ~ (v1_relat_1 @ X1)
% 0.40/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.61  thf(dt_k7_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X1)
% 0.40/0.61          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.40/0.61              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.40/0.61      inference('clc', [status(thm)], ['8', '9'])).
% 0.40/0.61  thf(t94_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X28 : $i, X29 : $i]:
% 0.40/0.61         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 0.40/0.61          | ~ (v1_relat_1 @ X29))),
% 0.40/0.61      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.40/0.61  thf(t76_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.40/0.61         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X24 : $i, X25 : $i]:
% 0.40/0.61         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X25) @ X24) @ X24)
% 0.40/0.61          | ~ (v1_relat_1 @ X24))),
% 0.40/0.61      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1)
% 0.40/0.61          | ~ (v1_relat_1 @ X1)
% 0.40/0.61          | ~ (v1_relat_1 @ X1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X1) | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['13'])).
% 0.40/0.61  thf(t179_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ![C:$i]:
% 0.40/0.61         ( ( v1_relat_1 @ C ) =>
% 0.40/0.61           ( ( r1_tarski @ B @ C ) =>
% 0.40/0.61             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X21)
% 0.40/0.61          | (r1_tarski @ (k10_relat_1 @ X22 @ X23) @ (k10_relat_1 @ X21 @ X23))
% 0.40/0.61          | ~ (r1_tarski @ X22 @ X21)
% 0.40/0.61          | ~ (v1_relat_1 @ X22))),
% 0.40/0.61      inference('cnf', [status(esa)], [t179_relat_1])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.40/0.61          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.40/0.61             (k10_relat_1 @ X0 @ X2))
% 0.40/0.61          | ~ (v1_relat_1 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.40/0.61           (k10_relat_1 @ X0 @ X2))
% 0.40/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.40/0.61          | ~ (v1_relat_1 @ X0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.40/0.61             (k10_relat_1 @ X0 @ X2)))),
% 0.40/0.61      inference('clc', [status(thm)], ['17', '18'])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.40/0.61           (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.40/0.61          | ~ (v1_relat_1 @ X1)
% 0.40/0.61          | ~ (v1_relat_1 @ X1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['10', '19'])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X1)
% 0.40/0.61          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.40/0.61             (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.40/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.61      inference('sup+', [status(thm)], ['5', '21'])).
% 0.40/0.61  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
