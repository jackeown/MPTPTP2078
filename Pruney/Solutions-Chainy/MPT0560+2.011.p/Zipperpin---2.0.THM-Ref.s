%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j1ngTgfTnJ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:39 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 104 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  655 ( 821 expanded)
%              Number of equality atoms :   46 (  58 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('6',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( ( k7_relat_1 @ X23 @ X24 )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X19 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( ( k6_relat_1 @ sk_B )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,
    ( ( k6_relat_1 @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','21','22'])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ ( k7_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ ( k7_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ ( k7_relat_1 @ X2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','33'])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k6_relat_1 @ sk_B )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('45',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k9_relat_1 @ X14 @ ( k9_relat_1 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j1ngTgfTnJ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 326 iterations in 0.214s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.44/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.44/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(t94_relat_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ B ) =>
% 0.44/0.66       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      (![X21 : $i, X22 : $i]:
% 0.44/0.66         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 0.44/0.66          | ~ (v1_relat_1 @ X22))),
% 0.44/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.44/0.66  thf(t71_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.44/0.66       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.44/0.66  thf('1', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.44/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.44/0.66  thf(t98_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (![X25 : $i]:
% 0.44/0.66         (((k7_relat_1 @ X25 @ (k1_relat_1 @ X25)) = (X25))
% 0.44/0.66          | ~ (v1_relat_1 @ X25))),
% 0.44/0.66      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.44/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.44/0.66  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.44/0.66  thf('4', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.44/0.66  thf(t162_relat_1, conjecture,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ![B:$i,C:$i]:
% 0.44/0.66         ( ( r1_tarski @ B @ C ) =>
% 0.44/0.66           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.44/0.66             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i]:
% 0.44/0.66        ( ( v1_relat_1 @ A ) =>
% 0.44/0.66          ( ![B:$i,C:$i]:
% 0.44/0.66            ( ( r1_tarski @ B @ C ) =>
% 0.44/0.66              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.44/0.66                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 0.44/0.66  thf('6', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('7', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.44/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.44/0.66  thf(t97_relat_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ B ) =>
% 0.44/0.66       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.44/0.66         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X23 : $i, X24 : $i]:
% 0.44/0.66         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.44/0.66          | ((k7_relat_1 @ X23 @ X24) = (X23))
% 0.44/0.66          | ~ (v1_relat_1 @ X23))),
% 0.44/0.66      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.44/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.44/0.66          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.66  thf('10', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.66  thf('11', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.44/0.66          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.44/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      (((k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.44/0.66      inference('sup-', [status(thm)], ['6', '11'])).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      (![X21 : $i, X22 : $i]:
% 0.44/0.66         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 0.44/0.66          | ~ (v1_relat_1 @ X22))),
% 0.44/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.44/0.66  thf(t76_relat_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ B ) =>
% 0.44/0.66       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.44/0.66         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X19 : $i, X20 : $i]:
% 0.44/0.66         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X20) @ X19) @ X19)
% 0.44/0.66          | ~ (v1_relat_1 @ X19))),
% 0.44/0.66      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.44/0.66  thf(d10_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      (![X0 : $i, X2 : $i]:
% 0.44/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.66  thf('16', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X0)
% 0.44/0.66          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.44/0.66          | ((X0) = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (r1_tarski @ X1 @ (k7_relat_1 @ X1 @ X0))
% 0.44/0.66          | ~ (v1_relat_1 @ X1)
% 0.44/0.66          | ((X1) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.44/0.66          | ~ (v1_relat_1 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['13', '16'])).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((X1) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.44/0.66          | ~ (v1_relat_1 @ X1)
% 0.44/0.66          | ~ (r1_tarski @ X1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.44/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      ((~ (r1_tarski @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_B))
% 0.44/0.66        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.44/0.66        | ((k6_relat_1 @ sk_B)
% 0.44/0.66            = (k5_relat_1 @ (k6_relat_1 @ sk_C) @ (k6_relat_1 @ sk_B))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['12', '18'])).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.44/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.67  thf('21', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.44/0.67      inference('simplify', [status(thm)], ['20'])).
% 0.44/0.67  thf('22', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.67  thf('23', plain,
% 0.44/0.67      (((k6_relat_1 @ sk_B)
% 0.44/0.67         = (k5_relat_1 @ (k6_relat_1 @ sk_C) @ (k6_relat_1 @ sk_B)))),
% 0.44/0.67      inference('demod', [status(thm)], ['19', '21', '22'])).
% 0.44/0.67  thf(t112_relat_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( v1_relat_1 @ B ) =>
% 0.44/0.67       ( ![C:$i]:
% 0.44/0.67         ( ( v1_relat_1 @ C ) =>
% 0.44/0.67           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.44/0.67             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.44/0.67  thf('24', plain,
% 0.44/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X9)
% 0.44/0.67          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.44/0.67              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 0.44/0.67          | ~ (v1_relat_1 @ X10))),
% 0.44/0.67      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.44/0.67  thf('25', plain,
% 0.44/0.67      (![X19 : $i, X20 : $i]:
% 0.44/0.67         ((r1_tarski @ (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) @ X19)
% 0.44/0.67          | ~ (v1_relat_1 @ X19))),
% 0.44/0.67      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.44/0.67  thf('26', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         ((r1_tarski @ 
% 0.44/0.67           (k7_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0) @ 
% 0.44/0.67           (k7_relat_1 @ X2 @ X0))
% 0.44/0.67          | ~ (v1_relat_1 @ X2)
% 0.44/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.44/0.67          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X0)))),
% 0.44/0.67      inference('sup+', [status(thm)], ['24', '25'])).
% 0.44/0.67  thf('27', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.67  thf('28', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         ((r1_tarski @ 
% 0.44/0.67           (k7_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0) @ 
% 0.44/0.67           (k7_relat_1 @ X2 @ X0))
% 0.44/0.67          | ~ (v1_relat_1 @ X2)
% 0.44/0.67          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X0)))),
% 0.44/0.67      inference('demod', [status(thm)], ['26', '27'])).
% 0.44/0.67  thf(dt_k7_relat_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.44/0.67  thf('29', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.44/0.67  thf('30', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X2)
% 0.44/0.67          | (r1_tarski @ 
% 0.44/0.67             (k7_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0) @ 
% 0.44/0.67             (k7_relat_1 @ X2 @ X0)))),
% 0.44/0.67      inference('clc', [status(thm)], ['28', '29'])).
% 0.44/0.67  thf('31', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 0.44/0.67           (k7_relat_1 @ (k6_relat_1 @ sk_C) @ X0))
% 0.44/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C)))),
% 0.44/0.67      inference('sup+', [status(thm)], ['23', '30'])).
% 0.44/0.67  thf('32', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.67  thf('33', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 0.44/0.67          (k7_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.67  thf('34', plain,
% 0.44/0.67      ((r1_tarski @ (k6_relat_1 @ sk_B) @ 
% 0.44/0.67        (k7_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 0.44/0.67      inference('sup+', [status(thm)], ['5', '33'])).
% 0.44/0.67  thf('35', plain,
% 0.44/0.67      (![X21 : $i, X22 : $i]:
% 0.44/0.67         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 0.44/0.67          | ~ (v1_relat_1 @ X22))),
% 0.44/0.67      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.44/0.67  thf('36', plain,
% 0.44/0.67      (![X19 : $i, X20 : $i]:
% 0.44/0.67         ((r1_tarski @ (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) @ X19)
% 0.44/0.67          | ~ (v1_relat_1 @ X19))),
% 0.44/0.67      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.44/0.67  thf('37', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.44/0.67           (k6_relat_1 @ X0))
% 0.44/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.44/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.44/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.44/0.67  thf('38', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.67  thf('39', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.67  thf('40', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.44/0.67  thf('41', plain,
% 0.44/0.67      (![X0 : $i, X2 : $i]:
% 0.44/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.67  thf('42', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 0.44/0.67             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.44/0.67          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.44/0.67  thf('43', plain,
% 0.44/0.67      (((k6_relat_1 @ sk_B) = (k7_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 0.44/0.67      inference('sup-', [status(thm)], ['34', '42'])).
% 0.44/0.67  thf(t148_relat_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( v1_relat_1 @ B ) =>
% 0.44/0.67       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.44/0.67  thf('44', plain,
% 0.44/0.67      (![X12 : $i, X13 : $i]:
% 0.44/0.67         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.44/0.67          | ~ (v1_relat_1 @ X12))),
% 0.44/0.67      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.44/0.67  thf('45', plain,
% 0.44/0.67      ((((k2_relat_1 @ (k6_relat_1 @ sk_B))
% 0.44/0.67          = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))
% 0.44/0.67        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C)))),
% 0.44/0.67      inference('sup+', [status(thm)], ['43', '44'])).
% 0.44/0.67  thf('46', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.44/0.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.44/0.67  thf('47', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.67  thf('48', plain, (((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 0.44/0.67      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.44/0.67  thf(t159_relat_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( v1_relat_1 @ B ) =>
% 0.44/0.67       ( ![C:$i]:
% 0.44/0.67         ( ( v1_relat_1 @ C ) =>
% 0.44/0.67           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.44/0.67             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.44/0.67  thf('49', plain,
% 0.44/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X14)
% 0.44/0.67          | ((k9_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 0.44/0.67              = (k9_relat_1 @ X14 @ (k9_relat_1 @ X15 @ X16)))
% 0.44/0.67          | ~ (v1_relat_1 @ X15))),
% 0.44/0.67      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.44/0.67  thf('50', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 0.44/0.67            = (k9_relat_1 @ X0 @ sk_B))
% 0.44/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['48', '49'])).
% 0.44/0.67  thf('51', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.67  thf('52', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 0.44/0.67            = (k9_relat_1 @ X0 @ sk_B))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['50', '51'])).
% 0.44/0.67  thf('53', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 0.44/0.67            = (k9_relat_1 @ X0 @ sk_B))
% 0.44/0.67          | ~ (v1_relat_1 @ X0)
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['0', '52'])).
% 0.44/0.67  thf('54', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X0)
% 0.44/0.67          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 0.44/0.67              = (k9_relat_1 @ X0 @ sk_B)))),
% 0.44/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.44/0.67  thf('55', plain,
% 0.44/0.67      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.44/0.67         != (k9_relat_1 @ sk_A @ sk_B))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('56', plain,
% 0.44/0.67      ((((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))
% 0.44/0.67        | ~ (v1_relat_1 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['54', '55'])).
% 0.44/0.67  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('58', plain,
% 0.44/0.67      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 0.44/0.67      inference('demod', [status(thm)], ['56', '57'])).
% 0.44/0.67  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.44/0.67  
% 0.44/0.67  % SZS output end Refutation
% 0.44/0.67  
% 0.49/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
