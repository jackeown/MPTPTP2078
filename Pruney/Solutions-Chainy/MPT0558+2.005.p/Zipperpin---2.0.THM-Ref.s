%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QxsZJO8nlv

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:35 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   57 (  63 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  521 ( 586 expanded)
%              Number of equality atoms :   34 (  39 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
        = ( k9_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X19 ) @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) @ X14 )
        = ( k5_relat_1 @ X13 @ ( k5_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X19 ) @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

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

thf('29',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
     != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QxsZJO8nlv
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 364 iterations in 0.318s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.77  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.77  thf(t148_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ B ) =>
% 0.59/0.77       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 0.59/0.77          | ~ (v1_relat_1 @ X6))),
% 0.59/0.77      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.77  thf(t94_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ B ) =>
% 0.59/0.77       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i]:
% 0.59/0.77         (((k7_relat_1 @ X20 @ X19) = (k5_relat_1 @ (k6_relat_1 @ X19) @ X20))
% 0.59/0.77          | ~ (v1_relat_1 @ X20))),
% 0.59/0.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.59/0.77  thf(d10_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.77  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.77      inference('simplify', [status(thm)], ['2'])).
% 0.59/0.77  thf(t79_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ B ) =>
% 0.59/0.77       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.59/0.77         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X17 : $i, X18 : $i]:
% 0.59/0.77         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.59/0.77          | ((k5_relat_1 @ X17 @ (k6_relat_1 @ X18)) = (X17))
% 0.59/0.77          | ~ (v1_relat_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf(t55_relat_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( v1_relat_1 @ B ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( v1_relat_1 @ C ) =>
% 0.59/0.77               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.59/0.77                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X12)
% 0.59/0.77          | ((k5_relat_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 0.59/0.77              = (k5_relat_1 @ X13 @ (k5_relat_1 @ X12 @ X14)))
% 0.59/0.77          | ~ (v1_relat_1 @ X14)
% 0.59/0.77          | ~ (v1_relat_1 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ X1)
% 0.59/0.77            = (k5_relat_1 @ X0 @ 
% 0.59/0.77               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.59/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.77  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.59/0.77  thf('8', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ X1)
% 0.59/0.77            = (k5_relat_1 @ X0 @ 
% 0.59/0.77               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('demod', [status(thm)], ['7', '8'])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k5_relat_1 @ X0 @ X1)
% 0.59/0.77              = (k5_relat_1 @ X0 @ 
% 0.59/0.77                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['9'])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ X1)
% 0.59/0.77            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('sup+', [status(thm)], ['1', '10'])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ((k5_relat_1 @ X0 @ X1)
% 0.59/0.77              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['11'])).
% 0.59/0.77  thf(dt_k7_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X4 : $i, X5 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X4) | (v1_relat_1 @ (k7_relat_1 @ X4 @ X5)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i]:
% 0.59/0.77         (((k7_relat_1 @ X20 @ X19) = (k5_relat_1 @ (k6_relat_1 @ X19) @ X20))
% 0.59/0.77          | ~ (v1_relat_1 @ X20))),
% 0.59/0.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.59/0.77  thf(t44_relat_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( v1_relat_1 @ B ) =>
% 0.59/0.77           ( r1_tarski @
% 0.59/0.77             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X8)
% 0.59/0.77          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 0.59/0.77             (k1_relat_1 @ X9))
% 0.59/0.77          | ~ (v1_relat_1 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.59/0.77           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.77  thf(t71_relat_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.59/0.77       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.59/0.77  thf('17', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.59/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.77  thf('18', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['19'])).
% 0.59/0.77  thf(t47_relat_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( v1_relat_1 @ B ) =>
% 0.59/0.77           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.59/0.77             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X10 : $i, X11 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X10)
% 0.59/0.77          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X11)) = (k2_relat_1 @ X11))
% 0.59/0.77          | ~ (r1_tarski @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X10))
% 0.59/0.77          | ~ (v1_relat_1 @ X11))),
% 0.59/0.77      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.59/0.77          | ((k2_relat_1 @ 
% 0.59/0.77              (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.77              = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ 
% 0.59/0.77              (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.77              = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['13', '22'])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k2_relat_1 @ 
% 0.59/0.77            (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.77            = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.59/0.77            = (k2_relat_1 @ (k7_relat_1 @ X0 @ (k2_relat_1 @ X1))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('sup+', [status(thm)], ['12', '24'])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.59/0.77              = (k2_relat_1 @ (k7_relat_1 @ X0 @ (k2_relat_1 @ X1)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['25'])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.59/0.77            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['0', '26'])).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.59/0.77              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['27'])).
% 0.59/0.77  thf(t160_relat_1, conjecture,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( v1_relat_1 @ B ) =>
% 0.59/0.77           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.59/0.77             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i]:
% 0.59/0.77        ( ( v1_relat_1 @ A ) =>
% 0.59/0.77          ( ![B:$i]:
% 0.59/0.77            ( ( v1_relat_1 @ B ) =>
% 0.59/0.77              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.59/0.77                ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t160_relat_1])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.59/0.77         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.59/0.77          != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.59/0.77        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.77        | ~ (v1_relat_1 @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.77  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      (((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.59/0.77         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.59/0.77  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
