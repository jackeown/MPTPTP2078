%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMhIshyejW

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:34 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   67 (  75 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :   17
%              Number of atoms          :  653 ( 739 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) @ X18 )
        = ( k5_relat_1 @ X17 @ ( k5_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X8: $i] :
      ( ( ( k9_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k9_relat_1 @ X11 @ ( k9_relat_1 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ X1 @ X2 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ X1 @ X2 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

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

thf('38',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
     != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMhIshyejW
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.07/1.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.33  % Solved by: fo/fo7.sh
% 1.07/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.33  % done 946 iterations in 0.882s
% 1.07/1.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.33  % SZS output start Refutation
% 1.07/1.33  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.07/1.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.33  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.07/1.33  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.07/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.33  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.07/1.33  thf(t94_relat_1, axiom,
% 1.07/1.33    (![A:$i,B:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ B ) =>
% 1.07/1.33       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.07/1.33  thf('0', plain,
% 1.07/1.33      (![X20 : $i, X21 : $i]:
% 1.07/1.33         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 1.07/1.33          | ~ (v1_relat_1 @ X21))),
% 1.07/1.33      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.07/1.33  thf(t80_relat_1, axiom,
% 1.07/1.33    (![A:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ A ) =>
% 1.07/1.33       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.07/1.33  thf('1', plain,
% 1.07/1.33      (![X19 : $i]:
% 1.07/1.33         (((k5_relat_1 @ X19 @ (k6_relat_1 @ (k2_relat_1 @ X19))) = (X19))
% 1.07/1.33          | ~ (v1_relat_1 @ X19))),
% 1.07/1.33      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.07/1.33  thf(t55_relat_1, axiom,
% 1.07/1.33    (![A:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ A ) =>
% 1.07/1.33       ( ![B:$i]:
% 1.07/1.33         ( ( v1_relat_1 @ B ) =>
% 1.07/1.33           ( ![C:$i]:
% 1.07/1.33             ( ( v1_relat_1 @ C ) =>
% 1.07/1.33               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.07/1.33                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.07/1.33  thf('2', plain,
% 1.07/1.33      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X16)
% 1.07/1.33          | ((k5_relat_1 @ (k5_relat_1 @ X17 @ X16) @ X18)
% 1.07/1.33              = (k5_relat_1 @ X17 @ (k5_relat_1 @ X16 @ X18)))
% 1.07/1.33          | ~ (v1_relat_1 @ X18)
% 1.07/1.33          | ~ (v1_relat_1 @ X17))),
% 1.07/1.33      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.07/1.33  thf('3', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (((k5_relat_1 @ X0 @ X1)
% 1.07/1.33            = (k5_relat_1 @ X0 @ 
% 1.07/1.33               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 1.07/1.33      inference('sup+', [status(thm)], ['1', '2'])).
% 1.07/1.33  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.07/1.33  thf('4', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 1.07/1.33      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.07/1.33  thf('5', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (((k5_relat_1 @ X0 @ X1)
% 1.07/1.33            = (k5_relat_1 @ X0 @ 
% 1.07/1.33               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1))),
% 1.07/1.33      inference('demod', [status(thm)], ['3', '4'])).
% 1.07/1.33  thf('6', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ((k5_relat_1 @ X0 @ X1)
% 1.07/1.33              = (k5_relat_1 @ X0 @ 
% 1.07/1.33                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 1.07/1.33      inference('simplify', [status(thm)], ['5'])).
% 1.07/1.33  thf('7', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (((k5_relat_1 @ X0 @ X1)
% 1.07/1.33            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1))),
% 1.07/1.33      inference('sup+', [status(thm)], ['0', '6'])).
% 1.07/1.33  thf('8', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ((k5_relat_1 @ X0 @ X1)
% 1.07/1.33              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 1.07/1.33      inference('simplify', [status(thm)], ['7'])).
% 1.07/1.33  thf(dt_k7_relat_1, axiom,
% 1.07/1.33    (![A:$i,B:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.07/1.33  thf('9', plain,
% 1.07/1.33      (![X6 : $i, X7 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 1.07/1.33      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.07/1.33  thf(t148_relat_1, axiom,
% 1.07/1.33    (![A:$i,B:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ B ) =>
% 1.07/1.33       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.07/1.33  thf('10', plain,
% 1.07/1.33      (![X9 : $i, X10 : $i]:
% 1.07/1.33         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 1.07/1.33          | ~ (v1_relat_1 @ X9))),
% 1.07/1.33      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.07/1.33  thf(t45_relat_1, axiom,
% 1.07/1.33    (![A:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ A ) =>
% 1.07/1.33       ( ![B:$i]:
% 1.07/1.33         ( ( v1_relat_1 @ B ) =>
% 1.07/1.33           ( r1_tarski @
% 1.07/1.33             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.07/1.33  thf('11', plain,
% 1.07/1.33      (![X14 : $i, X15 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X14)
% 1.07/1.33          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 1.07/1.33             (k2_relat_1 @ X14))
% 1.07/1.33          | ~ (v1_relat_1 @ X15))),
% 1.07/1.33      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.07/1.33  thf('12', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.33         ((r1_tarski @ 
% 1.07/1.33           (k2_relat_1 @ (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 1.07/1.33           (k9_relat_1 @ X1 @ X0))
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X2)
% 1.07/1.33          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.07/1.33      inference('sup+', [status(thm)], ['10', '11'])).
% 1.07/1.33  thf('13', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X2)
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | (r1_tarski @ 
% 1.07/1.33             (k2_relat_1 @ (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 1.07/1.33             (k9_relat_1 @ X1 @ X0)))),
% 1.07/1.33      inference('sup-', [status(thm)], ['9', '12'])).
% 1.07/1.33  thf('14', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.33         ((r1_tarski @ 
% 1.07/1.33           (k2_relat_1 @ (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 1.07/1.33           (k9_relat_1 @ X1 @ X0))
% 1.07/1.33          | ~ (v1_relat_1 @ X2)
% 1.07/1.33          | ~ (v1_relat_1 @ X1))),
% 1.07/1.33      inference('simplify', [status(thm)], ['13'])).
% 1.07/1.33  thf('15', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.07/1.33           (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1))),
% 1.07/1.33      inference('sup+', [status(thm)], ['8', '14'])).
% 1.07/1.33  thf('16', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.07/1.33             (k9_relat_1 @ X0 @ (k2_relat_1 @ X1))))),
% 1.07/1.33      inference('simplify', [status(thm)], ['15'])).
% 1.07/1.33  thf(t146_relat_1, axiom,
% 1.07/1.33    (![A:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ A ) =>
% 1.07/1.33       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.07/1.33  thf('17', plain,
% 1.07/1.33      (![X8 : $i]:
% 1.07/1.33         (((k9_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (k2_relat_1 @ X8))
% 1.07/1.33          | ~ (v1_relat_1 @ X8))),
% 1.07/1.33      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.07/1.33  thf(dt_k5_relat_1, axiom,
% 1.07/1.33    (![A:$i,B:$i]:
% 1.07/1.33     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.07/1.33       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.07/1.33  thf('18', plain,
% 1.07/1.33      (![X3 : $i, X4 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X3)
% 1.07/1.33          | ~ (v1_relat_1 @ X4)
% 1.07/1.33          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 1.07/1.33      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.07/1.33  thf(t159_relat_1, axiom,
% 1.07/1.33    (![A:$i,B:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ B ) =>
% 1.07/1.33       ( ![C:$i]:
% 1.07/1.33         ( ( v1_relat_1 @ C ) =>
% 1.07/1.33           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.07/1.33             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 1.07/1.33  thf('19', plain,
% 1.07/1.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X11)
% 1.07/1.33          | ((k9_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.07/1.33              = (k9_relat_1 @ X11 @ (k9_relat_1 @ X12 @ X13)))
% 1.07/1.33          | ~ (v1_relat_1 @ X12))),
% 1.07/1.33      inference('cnf', [status(esa)], [t159_relat_1])).
% 1.07/1.33  thf('20', plain,
% 1.07/1.33      (![X9 : $i, X10 : $i]:
% 1.07/1.33         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 1.07/1.33          | ~ (v1_relat_1 @ X9))),
% 1.07/1.33      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.07/1.33  thf('21', plain,
% 1.07/1.33      (![X20 : $i, X21 : $i]:
% 1.07/1.33         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 1.07/1.33          | ~ (v1_relat_1 @ X21))),
% 1.07/1.33      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.07/1.33  thf('22', plain,
% 1.07/1.33      (![X14 : $i, X15 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X14)
% 1.07/1.33          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 1.07/1.33             (k2_relat_1 @ X14))
% 1.07/1.33          | ~ (v1_relat_1 @ X15))),
% 1.07/1.33      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.07/1.33  thf('23', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.07/1.33           (k2_relat_1 @ X1))
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.07/1.33          | ~ (v1_relat_1 @ X1))),
% 1.07/1.33      inference('sup+', [status(thm)], ['21', '22'])).
% 1.07/1.33  thf('24', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 1.07/1.33      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.07/1.33  thf('25', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.07/1.33           (k2_relat_1 @ X1))
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X1))),
% 1.07/1.33      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.33  thf('26', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X1)
% 1.07/1.33          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.07/1.33             (k2_relat_1 @ X1)))),
% 1.07/1.33      inference('simplify', [status(thm)], ['25'])).
% 1.07/1.33  thf('27', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X1))),
% 1.07/1.33      inference('sup+', [status(thm)], ['20', '26'])).
% 1.07/1.33  thf('28', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X1)
% 1.07/1.33          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 1.07/1.33      inference('simplify', [status(thm)], ['27'])).
% 1.07/1.33  thf('29', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.33         ((r1_tarski @ (k9_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0)) @ 
% 1.07/1.33           (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X2)
% 1.07/1.33          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X2)))),
% 1.07/1.33      inference('sup+', [status(thm)], ['19', '28'])).
% 1.07/1.33  thf('30', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | (r1_tarski @ (k9_relat_1 @ X0 @ (k9_relat_1 @ X1 @ X2)) @ 
% 1.07/1.33             (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.07/1.33      inference('sup-', [status(thm)], ['18', '29'])).
% 1.07/1.33  thf('31', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.33         ((r1_tarski @ (k9_relat_1 @ X0 @ (k9_relat_1 @ X1 @ X2)) @ 
% 1.07/1.33           (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0))),
% 1.07/1.33      inference('simplify', [status(thm)], ['30'])).
% 1.07/1.33  thf('32', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         ((r1_tarski @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ 
% 1.07/1.33           (k2_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0))),
% 1.07/1.33      inference('sup+', [status(thm)], ['17', '31'])).
% 1.07/1.33  thf('33', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | (r1_tarski @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ 
% 1.07/1.33             (k2_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 1.07/1.33      inference('simplify', [status(thm)], ['32'])).
% 1.07/1.33  thf(d10_xboole_0, axiom,
% 1.07/1.33    (![A:$i,B:$i]:
% 1.07/1.33     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.07/1.33  thf('34', plain,
% 1.07/1.33      (![X0 : $i, X2 : $i]:
% 1.07/1.33         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.07/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.07/1.33  thf('35', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.07/1.33               (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 1.07/1.33          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.07/1.33              = (k9_relat_1 @ X0 @ (k2_relat_1 @ X1))))),
% 1.07/1.33      inference('sup-', [status(thm)], ['33', '34'])).
% 1.07/1.33  thf('36', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 1.07/1.33              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 1.07/1.33          | ~ (v1_relat_1 @ X1)
% 1.07/1.33          | ~ (v1_relat_1 @ X0))),
% 1.07/1.33      inference('sup-', [status(thm)], ['16', '35'])).
% 1.07/1.33  thf('37', plain,
% 1.07/1.33      (![X0 : $i, X1 : $i]:
% 1.07/1.33         (((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 1.07/1.33            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 1.07/1.33          | ~ (v1_relat_1 @ X0)
% 1.07/1.33          | ~ (v1_relat_1 @ X1))),
% 1.07/1.33      inference('simplify', [status(thm)], ['36'])).
% 1.07/1.33  thf(t160_relat_1, conjecture,
% 1.07/1.33    (![A:$i]:
% 1.07/1.33     ( ( v1_relat_1 @ A ) =>
% 1.07/1.33       ( ![B:$i]:
% 1.07/1.33         ( ( v1_relat_1 @ B ) =>
% 1.07/1.33           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.07/1.33             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.07/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.33    (~( ![A:$i]:
% 1.07/1.33        ( ( v1_relat_1 @ A ) =>
% 1.07/1.33          ( ![B:$i]:
% 1.07/1.33            ( ( v1_relat_1 @ B ) =>
% 1.07/1.33              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.07/1.33                ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 1.07/1.33    inference('cnf.neg', [status(esa)], [t160_relat_1])).
% 1.07/1.33  thf('38', plain,
% 1.07/1.33      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.07/1.33         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 1.07/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.33  thf('39', plain,
% 1.07/1.33      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 1.07/1.33          != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 1.07/1.33        | ~ (v1_relat_1 @ sk_B)
% 1.07/1.33        | ~ (v1_relat_1 @ sk_A))),
% 1.07/1.33      inference('sup-', [status(thm)], ['37', '38'])).
% 1.07/1.33  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 1.07/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.33  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 1.07/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.33  thf('42', plain,
% 1.07/1.33      (((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 1.07/1.33         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 1.07/1.33      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.07/1.33  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 1.07/1.33  
% 1.07/1.33  % SZS output end Refutation
% 1.07/1.33  
% 1.19/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
