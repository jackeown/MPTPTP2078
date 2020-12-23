%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Zqy1LIhRO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:36 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  446 ( 514 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k9_relat_1 @ X5 @ ( k9_relat_1 @ X6 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X11 ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t160_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t160_relat_1])).

thf('22',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
     != ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Zqy1LIhRO
% 0.17/0.37  % Computer   : n021.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 12:44:04 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 19 iterations in 0.021s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.24/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.24/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.50  thf(t146_relat_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ A ) =>
% 0.24/0.50       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (![X2 : $i]:
% 0.24/0.50         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 0.24/0.50          | ~ (v1_relat_1 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.24/0.50  thf(t159_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ B ) =>
% 0.24/0.50       ( ![C:$i]:
% 0.24/0.50         ( ( v1_relat_1 @ C ) =>
% 0.24/0.50           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.24/0.50             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X5)
% 0.24/0.50          | ((k9_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.24/0.50              = (k9_relat_1 @ X5 @ (k9_relat_1 @ X6 @ X7)))
% 0.24/0.50          | ~ (v1_relat_1 @ X6))),
% 0.24/0.50      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (((k9_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.24/0.50            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.24/0.50          | ~ (v1_relat_1 @ X0)
% 0.24/0.50          | ~ (v1_relat_1 @ X0)
% 0.24/0.50          | ~ (v1_relat_1 @ X1))),
% 0.24/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X1)
% 0.24/0.50          | ~ (v1_relat_1 @ X0)
% 0.24/0.50          | ((k9_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.24/0.50              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 0.24/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.24/0.50  thf(dt_k5_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.24/0.50       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X0)
% 0.24/0.50          | ~ (v1_relat_1 @ X1)
% 0.24/0.50          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.24/0.50      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X0)
% 0.24/0.50          | ~ (v1_relat_1 @ X1)
% 0.24/0.50          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.24/0.50      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X0)
% 0.24/0.50          | ~ (v1_relat_1 @ X1)
% 0.24/0.50          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.24/0.50      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.24/0.50  thf(t44_relat_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ A ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( v1_relat_1 @ B ) =>
% 0.24/0.50           ( r1_tarski @
% 0.24/0.50             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X8 : $i, X9 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X8)
% 0.24/0.50          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 0.24/0.50             (k1_relat_1 @ X9))
% 0.24/0.50          | ~ (v1_relat_1 @ X9))),
% 0.24/0.50      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.24/0.50  thf(t77_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ B ) =>
% 0.24/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.24/0.50         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X10 : $i, X11 : $i]:
% 0.24/0.50         (~ (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.24/0.50          | ((k5_relat_1 @ (k6_relat_1 @ X11) @ X10) = (X10))
% 0.24/0.50          | ~ (v1_relat_1 @ X10))),
% 0.24/0.50      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X0)
% 0.24/0.50          | ~ (v1_relat_1 @ X1)
% 0.24/0.50          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.24/0.50          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.24/0.50              (k5_relat_1 @ X0 @ X1)) = (k5_relat_1 @ X0 @ X1)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ 
% 0.24/0.51              (k5_relat_1 @ X1 @ X0)) = (k5_relat_1 @ X1 @ X0))
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['6', '9'])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ 
% 0.24/0.51            (k5_relat_1 @ X1 @ X0)) = (k5_relat_1 @ X1 @ X0))
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X0))),
% 0.24/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.24/0.51  thf(t94_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ B ) =>
% 0.24/0.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X12 : $i, X13 : $i]:
% 0.24/0.51         (((k7_relat_1 @ X13 @ X12) = (k5_relat_1 @ (k6_relat_1 @ X12) @ X13))
% 0.24/0.51          | ~ (v1_relat_1 @ X13))),
% 0.24/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((k7_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X1))
% 0.24/0.51            = (k5_relat_1 @ X1 @ X0))
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.24/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ((k7_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X1))
% 0.24/0.51              = (k5_relat_1 @ X1 @ X0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['5', '13'])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((k7_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X1))
% 0.24/0.51            = (k5_relat_1 @ X1 @ X0))
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X0))),
% 0.24/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.24/0.51  thf(t148_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ B ) =>
% 0.24/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.24/0.51  thf('16', plain,
% 0.24/0.51      (![X3 : $i, X4 : $i]:
% 0.24/0.51         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.24/0.51          | ~ (v1_relat_1 @ X3))),
% 0.24/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.24/0.51            = (k9_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X1)))
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.24/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.24/0.51              = (k9_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X1))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['4', '17'])).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.24/0.51            = (k9_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X1)))
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X0))),
% 0.24/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.24/0.51  thf('20', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.24/0.51            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X0))),
% 0.24/0.51      inference('sup+', [status(thm)], ['3', '19'])).
% 0.24/0.51  thf('21', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.24/0.51              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.24/0.51  thf(t160_relat_1, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ A ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( v1_relat_1 @ B ) =>
% 0.24/0.51           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.24/0.51             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ( v1_relat_1 @ A ) =>
% 0.24/0.51          ( ![B:$i]:
% 0.24/0.51            ( ( v1_relat_1 @ B ) =>
% 0.24/0.51              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.24/0.51                ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t160_relat_1])).
% 0.24/0.51  thf('22', plain,
% 0.24/0.51      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.24/0.51         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('23', plain,
% 0.24/0.51      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.24/0.51          != (k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.24/0.51        | ~ (v1_relat_1 @ sk_A)
% 0.24/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.51  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('26', plain,
% 0.24/0.51      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.24/0.51         != (k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.24/0.51  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
