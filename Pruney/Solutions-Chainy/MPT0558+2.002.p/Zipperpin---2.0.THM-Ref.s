%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0LhDEeUpvE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:34 EST 2020

% Result     : Theorem 3.32s
% Output     : Refutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   62 (  70 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :   15
%              Number of atoms          :  563 ( 641 expanded)
%              Number of equality atoms :   35 (  41 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
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

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X19 ) @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

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

thf('34',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
     != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0LhDEeUpvE
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:59:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.32/3.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.32/3.59  % Solved by: fo/fo7.sh
% 3.32/3.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.32/3.59  % done 3514 iterations in 3.136s
% 3.32/3.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.32/3.59  % SZS output start Refutation
% 3.32/3.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.32/3.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.32/3.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.32/3.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.32/3.59  thf(sk_A_type, type, sk_A: $i).
% 3.32/3.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.32/3.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.32/3.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.32/3.59  thf(sk_B_type, type, sk_B: $i).
% 3.32/3.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.32/3.59  thf(t148_relat_1, axiom,
% 3.32/3.59    (![A:$i,B:$i]:
% 3.32/3.59     ( ( v1_relat_1 @ B ) =>
% 3.32/3.59       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.32/3.59  thf('0', plain,
% 3.32/3.59      (![X6 : $i, X7 : $i]:
% 3.32/3.59         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 3.32/3.59          | ~ (v1_relat_1 @ X6))),
% 3.32/3.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.32/3.59  thf(t94_relat_1, axiom,
% 3.32/3.59    (![A:$i,B:$i]:
% 3.32/3.59     ( ( v1_relat_1 @ B ) =>
% 3.32/3.59       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 3.32/3.59  thf('1', plain,
% 3.32/3.59      (![X19 : $i, X20 : $i]:
% 3.32/3.59         (((k7_relat_1 @ X20 @ X19) = (k5_relat_1 @ (k6_relat_1 @ X19) @ X20))
% 3.32/3.59          | ~ (v1_relat_1 @ X20))),
% 3.32/3.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.32/3.59  thf(d10_xboole_0, axiom,
% 3.32/3.59    (![A:$i,B:$i]:
% 3.32/3.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.32/3.59  thf('2', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.32/3.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.32/3.59  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.32/3.59      inference('simplify', [status(thm)], ['2'])).
% 3.32/3.59  thf(t79_relat_1, axiom,
% 3.32/3.59    (![A:$i,B:$i]:
% 3.32/3.59     ( ( v1_relat_1 @ B ) =>
% 3.32/3.59       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.32/3.59         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 3.32/3.59  thf('4', plain,
% 3.32/3.59      (![X17 : $i, X18 : $i]:
% 3.32/3.59         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 3.32/3.59          | ((k5_relat_1 @ X17 @ (k6_relat_1 @ X18)) = (X17))
% 3.32/3.59          | ~ (v1_relat_1 @ X17))),
% 3.32/3.59      inference('cnf', [status(esa)], [t79_relat_1])).
% 3.32/3.59  thf('5', plain,
% 3.32/3.59      (![X0 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X0)
% 3.32/3.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 3.32/3.59      inference('sup-', [status(thm)], ['3', '4'])).
% 3.32/3.59  thf(t55_relat_1, axiom,
% 3.32/3.59    (![A:$i]:
% 3.32/3.59     ( ( v1_relat_1 @ A ) =>
% 3.32/3.59       ( ![B:$i]:
% 3.32/3.59         ( ( v1_relat_1 @ B ) =>
% 3.32/3.59           ( ![C:$i]:
% 3.32/3.59             ( ( v1_relat_1 @ C ) =>
% 3.32/3.59               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 3.32/3.59                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.32/3.59  thf('6', plain,
% 3.32/3.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X12)
% 3.32/3.59          | ((k5_relat_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 3.32/3.59              = (k5_relat_1 @ X13 @ (k5_relat_1 @ X12 @ X14)))
% 3.32/3.59          | ~ (v1_relat_1 @ X14)
% 3.32/3.59          | ~ (v1_relat_1 @ X13))),
% 3.32/3.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.32/3.59  thf('7', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (((k5_relat_1 @ X0 @ X1)
% 3.32/3.59            = (k5_relat_1 @ X0 @ 
% 3.32/3.59               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 3.32/3.59      inference('sup+', [status(thm)], ['5', '6'])).
% 3.32/3.59  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 3.32/3.59  thf('8', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 3.32/3.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.32/3.59  thf('9', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (((k5_relat_1 @ X0 @ X1)
% 3.32/3.59            = (k5_relat_1 @ X0 @ 
% 3.32/3.59               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X1))),
% 3.32/3.59      inference('demod', [status(thm)], ['7', '8'])).
% 3.32/3.59  thf('10', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ((k5_relat_1 @ X0 @ X1)
% 3.32/3.59              = (k5_relat_1 @ X0 @ 
% 3.32/3.59                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 3.32/3.59      inference('simplify', [status(thm)], ['9'])).
% 3.32/3.59  thf('11', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (((k5_relat_1 @ X0 @ X1)
% 3.32/3.59            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X1))),
% 3.32/3.59      inference('sup+', [status(thm)], ['1', '10'])).
% 3.32/3.59  thf('12', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ((k5_relat_1 @ X0 @ X1)
% 3.32/3.59              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 3.32/3.59      inference('simplify', [status(thm)], ['11'])).
% 3.32/3.59  thf('13', plain,
% 3.32/3.59      (![X19 : $i, X20 : $i]:
% 3.32/3.59         (((k7_relat_1 @ X20 @ X19) = (k5_relat_1 @ (k6_relat_1 @ X19) @ X20))
% 3.32/3.59          | ~ (v1_relat_1 @ X20))),
% 3.32/3.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.32/3.59  thf(dt_k5_relat_1, axiom,
% 3.32/3.59    (![A:$i,B:$i]:
% 3.32/3.59     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 3.32/3.59       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 3.32/3.59  thf('14', plain,
% 3.32/3.59      (![X3 : $i, X4 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X3)
% 3.32/3.59          | ~ (v1_relat_1 @ X4)
% 3.32/3.59          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 3.32/3.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.32/3.59  thf('15', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.32/3.59      inference('sup+', [status(thm)], ['13', '14'])).
% 3.32/3.59  thf('16', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 3.32/3.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.32/3.59  thf('17', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ X1))),
% 3.32/3.59      inference('demod', [status(thm)], ['15', '16'])).
% 3.32/3.59  thf('18', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.32/3.59      inference('simplify', [status(thm)], ['17'])).
% 3.32/3.59  thf('19', plain,
% 3.32/3.59      (![X19 : $i, X20 : $i]:
% 3.32/3.59         (((k7_relat_1 @ X20 @ X19) = (k5_relat_1 @ (k6_relat_1 @ X19) @ X20))
% 3.32/3.59          | ~ (v1_relat_1 @ X20))),
% 3.32/3.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.32/3.59  thf(t44_relat_1, axiom,
% 3.32/3.59    (![A:$i]:
% 3.32/3.59     ( ( v1_relat_1 @ A ) =>
% 3.32/3.59       ( ![B:$i]:
% 3.32/3.59         ( ( v1_relat_1 @ B ) =>
% 3.32/3.59           ( r1_tarski @
% 3.32/3.59             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 3.32/3.59  thf('20', plain,
% 3.32/3.59      (![X8 : $i, X9 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X8)
% 3.32/3.59          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 3.32/3.59             (k1_relat_1 @ X9))
% 3.32/3.59          | ~ (v1_relat_1 @ X9))),
% 3.32/3.59      inference('cnf', [status(esa)], [t44_relat_1])).
% 3.32/3.59  thf('21', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 3.32/3.59           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.32/3.59          | ~ (v1_relat_1 @ X1))),
% 3.32/3.59      inference('sup+', [status(thm)], ['19', '20'])).
% 3.32/3.59  thf(t71_relat_1, axiom,
% 3.32/3.59    (![A:$i]:
% 3.32/3.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.32/3.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.32/3.59  thf('22', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 3.32/3.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.32/3.59  thf('23', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 3.32/3.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.32/3.59  thf('24', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ X1))),
% 3.32/3.59      inference('demod', [status(thm)], ['21', '22', '23'])).
% 3.32/3.59  thf('25', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X1)
% 3.32/3.59          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 3.32/3.59      inference('simplify', [status(thm)], ['24'])).
% 3.32/3.59  thf(t47_relat_1, axiom,
% 3.32/3.59    (![A:$i]:
% 3.32/3.59     ( ( v1_relat_1 @ A ) =>
% 3.32/3.59       ( ![B:$i]:
% 3.32/3.59         ( ( v1_relat_1 @ B ) =>
% 3.32/3.59           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 3.32/3.59             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.32/3.59  thf('26', plain,
% 3.32/3.59      (![X10 : $i, X11 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X10)
% 3.32/3.59          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X11)) = (k2_relat_1 @ X11))
% 3.32/3.59          | ~ (r1_tarski @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X10))
% 3.32/3.59          | ~ (v1_relat_1 @ X11))),
% 3.32/3.59      inference('cnf', [status(esa)], [t47_relat_1])).
% 3.32/3.59  thf('27', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 3.32/3.59          | ((k2_relat_1 @ 
% 3.32/3.59              (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 3.32/3.59              = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 3.32/3.59          | ~ (v1_relat_1 @ X0))),
% 3.32/3.59      inference('sup-', [status(thm)], ['25', '26'])).
% 3.32/3.59  thf('28', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ((k2_relat_1 @ 
% 3.32/3.59              (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 3.32/3.59              = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 3.32/3.59          | ~ (v1_relat_1 @ X1))),
% 3.32/3.59      inference('sup-', [status(thm)], ['18', '27'])).
% 3.32/3.59  thf('29', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (((k2_relat_1 @ 
% 3.32/3.59            (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 3.32/3.59            = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X1))),
% 3.32/3.59      inference('simplify', [status(thm)], ['28'])).
% 3.32/3.59  thf('30', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.32/3.59            = (k2_relat_1 @ (k7_relat_1 @ X0 @ (k2_relat_1 @ X1))))
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ~ (v1_relat_1 @ X1))),
% 3.32/3.59      inference('sup+', [status(thm)], ['12', '29'])).
% 3.32/3.59  thf('31', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (~ (v1_relat_1 @ X1)
% 3.32/3.59          | ~ (v1_relat_1 @ X0)
% 3.32/3.59          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.32/3.59              = (k2_relat_1 @ (k7_relat_1 @ X0 @ (k2_relat_1 @ X1)))))),
% 3.32/3.59      inference('simplify', [status(thm)], ['30'])).
% 3.32/3.59  thf('32', plain,
% 3.32/3.59      (![X0 : $i, X1 : $i]:
% 3.32/3.59         (((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 3.43/3.59            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 3.43/3.59          | ~ (v1_relat_1 @ X1)
% 3.43/3.59          | ~ (v1_relat_1 @ X1)
% 3.43/3.59          | ~ (v1_relat_1 @ X0))),
% 3.43/3.59      inference('sup+', [status(thm)], ['0', '31'])).
% 3.43/3.59  thf('33', plain,
% 3.43/3.59      (![X0 : $i, X1 : $i]:
% 3.43/3.59         (~ (v1_relat_1 @ X0)
% 3.43/3.59          | ~ (v1_relat_1 @ X1)
% 3.43/3.59          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 3.43/3.59              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 3.43/3.59      inference('simplify', [status(thm)], ['32'])).
% 3.43/3.59  thf(t160_relat_1, conjecture,
% 3.43/3.59    (![A:$i]:
% 3.43/3.59     ( ( v1_relat_1 @ A ) =>
% 3.43/3.59       ( ![B:$i]:
% 3.43/3.59         ( ( v1_relat_1 @ B ) =>
% 3.43/3.59           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 3.43/3.59             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.43/3.59  thf(zf_stmt_0, negated_conjecture,
% 3.43/3.59    (~( ![A:$i]:
% 3.43/3.59        ( ( v1_relat_1 @ A ) =>
% 3.43/3.59          ( ![B:$i]:
% 3.43/3.59            ( ( v1_relat_1 @ B ) =>
% 3.43/3.59              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 3.43/3.59                ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 3.43/3.59    inference('cnf.neg', [status(esa)], [t160_relat_1])).
% 3.43/3.59  thf('34', plain,
% 3.43/3.59      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 3.43/3.59         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 3.43/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.43/3.59  thf('35', plain,
% 3.43/3.59      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 3.43/3.59          != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 3.43/3.59        | ~ (v1_relat_1 @ sk_B)
% 3.43/3.59        | ~ (v1_relat_1 @ sk_A))),
% 3.43/3.59      inference('sup-', [status(thm)], ['33', '34'])).
% 3.43/3.59  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 3.43/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.43/3.59  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 3.43/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.43/3.59  thf('38', plain,
% 3.43/3.59      (((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 3.43/3.59         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 3.43/3.59      inference('demod', [status(thm)], ['35', '36', '37'])).
% 3.43/3.59  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 3.43/3.59  
% 3.43/3.59  % SZS output end Refutation
% 3.43/3.59  
% 3.43/3.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
