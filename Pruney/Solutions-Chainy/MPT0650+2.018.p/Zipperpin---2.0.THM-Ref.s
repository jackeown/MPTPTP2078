%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YTLFAv4xC3

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:21 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 260 expanded)
%              Number of leaves         :   31 (  86 expanded)
%              Depth                    :   25
%              Number of atoms          : 1249 (3644 expanded)
%              Number of equality atoms :   88 ( 262 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('8',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('9',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('10',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( ( ( k5_relat_1 @ X17 @ ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k10_relat_1 @ X10 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
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

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k10_relat_1 @ X10 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X22 @ X23 ) @ X24 )
        = ( k1_funct_1 @ X23 @ ( k1_funct_1 @ X22 @ X24 ) ) )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('51',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['49','51'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ X28 )
      | ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('59',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['49','51'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X25 ) )
      | ( X26
        = ( k1_funct_1 @ ( k2_funct_1 @ X25 ) @ ( k1_funct_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','75'])).

thf('77',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['45','46','47','48','76'])).

thf('78',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('79',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('87',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('88',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('90',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('93',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['85','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YTLFAv4xC3
% 0.13/0.37  % Computer   : n023.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:40:51 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.37  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 1.87/2.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.87/2.07  % Solved by: fo/fo7.sh
% 1.87/2.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.87/2.07  % done 2601 iterations in 1.578s
% 1.87/2.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.87/2.07  % SZS output start Refutation
% 1.87/2.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.87/2.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.87/2.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.87/2.07  thf(sk_A_type, type, sk_A: $i).
% 1.87/2.07  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.87/2.07  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.87/2.07  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.87/2.07  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.87/2.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.87/2.07  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.87/2.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.87/2.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.87/2.07  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.87/2.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.87/2.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.87/2.07  thf(sk_B_type, type, sk_B: $i).
% 1.87/2.07  thf(t57_funct_1, conjecture,
% 1.87/2.07    (![A:$i,B:$i]:
% 1.87/2.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.87/2.07       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 1.87/2.07         ( ( ( A ) =
% 1.87/2.07             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 1.87/2.07           ( ( A ) =
% 1.87/2.07             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 1.87/2.07  thf(zf_stmt_0, negated_conjecture,
% 1.87/2.07    (~( ![A:$i,B:$i]:
% 1.87/2.07        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.87/2.07          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 1.87/2.07            ( ( ( A ) =
% 1.87/2.07                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 1.87/2.07              ( ( A ) =
% 1.87/2.07                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 1.87/2.07    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 1.87/2.07  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf(dt_k4_relat_1, axiom,
% 1.87/2.07    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.87/2.07  thf('1', plain,
% 1.87/2.07      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 1.87/2.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.87/2.07  thf(d9_funct_1, axiom,
% 1.87/2.07    (![A:$i]:
% 1.87/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.87/2.07       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.87/2.07  thf('2', plain,
% 1.87/2.07      (![X18 : $i]:
% 1.87/2.07         (~ (v2_funct_1 @ X18)
% 1.87/2.07          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 1.87/2.07          | ~ (v1_funct_1 @ X18)
% 1.87/2.07          | ~ (v1_relat_1 @ X18))),
% 1.87/2.07      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.87/2.07  thf(dt_k2_funct_1, axiom,
% 1.87/2.07    (![A:$i]:
% 1.87/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.87/2.07       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.87/2.07         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.87/2.07  thf('3', plain,
% 1.87/2.07      (![X19 : $i]:
% 1.87/2.07         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.87/2.07          | ~ (v1_funct_1 @ X19)
% 1.87/2.07          | ~ (v1_relat_1 @ X19))),
% 1.87/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.87/2.07  thf('4', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ~ (v2_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0))),
% 1.87/2.07      inference('sup+', [status(thm)], ['2', '3'])).
% 1.87/2.07  thf('5', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (~ (v2_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 1.87/2.07      inference('simplify', [status(thm)], ['4'])).
% 1.87/2.07  thf(involutiveness_k4_relat_1, axiom,
% 1.87/2.07    (![A:$i]:
% 1.87/2.07     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.87/2.07  thf('6', plain,
% 1.87/2.07      (![X8 : $i]:
% 1.87/2.07         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 1.87/2.07      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.87/2.07  thf(t37_relat_1, axiom,
% 1.87/2.07    (![A:$i]:
% 1.87/2.07     ( ( v1_relat_1 @ A ) =>
% 1.87/2.07       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.87/2.07         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.87/2.07  thf('7', plain,
% 1.87/2.07      (![X14 : $i]:
% 1.87/2.07         (((k1_relat_1 @ X14) = (k2_relat_1 @ (k4_relat_1 @ X14)))
% 1.87/2.07          | ~ (v1_relat_1 @ X14))),
% 1.87/2.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.87/2.07  thf('8', plain,
% 1.87/2.07      (![X14 : $i]:
% 1.87/2.07         (((k2_relat_1 @ X14) = (k1_relat_1 @ (k4_relat_1 @ X14)))
% 1.87/2.07          | ~ (v1_relat_1 @ X14))),
% 1.87/2.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.87/2.07  thf('9', plain,
% 1.87/2.07      (![X8 : $i]:
% 1.87/2.07         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 1.87/2.07      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.87/2.07  thf('10', plain,
% 1.87/2.07      (![X14 : $i]:
% 1.87/2.07         (((k1_relat_1 @ X14) = (k2_relat_1 @ (k4_relat_1 @ X14)))
% 1.87/2.07          | ~ (v1_relat_1 @ X14))),
% 1.87/2.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.87/2.07  thf(t80_relat_1, axiom,
% 1.87/2.07    (![A:$i]:
% 1.87/2.07     ( ( v1_relat_1 @ A ) =>
% 1.87/2.07       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.87/2.07  thf('11', plain,
% 1.87/2.07      (![X17 : $i]:
% 1.87/2.07         (((k5_relat_1 @ X17 @ (k6_relat_1 @ (k2_relat_1 @ X17))) = (X17))
% 1.87/2.07          | ~ (v1_relat_1 @ X17))),
% 1.87/2.07      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.87/2.07  thf('12', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.87/2.07            = (k4_relat_1 @ X0))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.87/2.07      inference('sup+', [status(thm)], ['10', '11'])).
% 1.87/2.07  thf('13', plain,
% 1.87/2.07      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 1.87/2.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.87/2.07  thf('14', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.87/2.07              = (k4_relat_1 @ X0)))),
% 1.87/2.07      inference('clc', [status(thm)], ['12', '13'])).
% 1.87/2.07  thf('15', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 1.87/2.07            = (k4_relat_1 @ (k4_relat_1 @ X0)))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.87/2.07      inference('sup+', [status(thm)], ['9', '14'])).
% 1.87/2.07  thf('16', plain,
% 1.87/2.07      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 1.87/2.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.87/2.07  thf('17', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 1.87/2.07              = (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 1.87/2.07      inference('clc', [status(thm)], ['15', '16'])).
% 1.87/2.07  thf('18', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.87/2.07            = (k4_relat_1 @ (k4_relat_1 @ X0)))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0))),
% 1.87/2.07      inference('sup+', [status(thm)], ['8', '17'])).
% 1.87/2.07  thf('19', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.87/2.07              = (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 1.87/2.07      inference('simplify', [status(thm)], ['18'])).
% 1.87/2.07  thf(t182_relat_1, axiom,
% 1.87/2.07    (![A:$i]:
% 1.87/2.07     ( ( v1_relat_1 @ A ) =>
% 1.87/2.07       ( ![B:$i]:
% 1.87/2.07         ( ( v1_relat_1 @ B ) =>
% 1.87/2.07           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.87/2.07             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.87/2.07  thf('20', plain,
% 1.87/2.07      (![X9 : $i, X10 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X9)
% 1.87/2.07          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 1.87/2.07              = (k10_relat_1 @ X10 @ (k1_relat_1 @ X9)))
% 1.87/2.07          | ~ (v1_relat_1 @ X10))),
% 1.87/2.07      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.87/2.07  thf('21', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 1.87/2.07            = (k10_relat_1 @ X0 @ 
% 1.87/2.07               (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 1.87/2.07      inference('sup+', [status(thm)], ['19', '20'])).
% 1.87/2.07  thf(t71_relat_1, axiom,
% 1.87/2.07    (![A:$i]:
% 1.87/2.07     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.87/2.07       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.87/2.07  thf('22', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 1.87/2.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.87/2.07  thf(fc3_funct_1, axiom,
% 1.87/2.07    (![A:$i]:
% 1.87/2.07     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.87/2.07       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.87/2.07  thf('23', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.87/2.07      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.87/2.07  thf('24', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 1.87/2.07            = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0))),
% 1.87/2.07      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.87/2.07  thf('25', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 1.87/2.07              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.87/2.07      inference('simplify', [status(thm)], ['24'])).
% 1.87/2.07  thf('26', plain,
% 1.87/2.07      (![X14 : $i]:
% 1.87/2.07         (((k2_relat_1 @ X14) = (k1_relat_1 @ (k4_relat_1 @ X14)))
% 1.87/2.07          | ~ (v1_relat_1 @ X14))),
% 1.87/2.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.87/2.07  thf('27', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (((k2_relat_1 @ (k4_relat_1 @ X0))
% 1.87/2.07            = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.87/2.07      inference('sup+', [status(thm)], ['25', '26'])).
% 1.87/2.07  thf('28', plain,
% 1.87/2.07      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 1.87/2.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.87/2.07  thf('29', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ((k2_relat_1 @ (k4_relat_1 @ X0))
% 1.87/2.07              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.87/2.07      inference('clc', [status(thm)], ['27', '28'])).
% 1.87/2.07  thf('30', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 1.87/2.07            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.87/2.07      inference('sup+', [status(thm)], ['7', '29'])).
% 1.87/2.07  thf('31', plain,
% 1.87/2.07      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 1.87/2.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.87/2.07  thf('32', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 1.87/2.07              = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 1.87/2.07      inference('clc', [status(thm)], ['30', '31'])).
% 1.87/2.07  thf('33', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (((k2_relat_1 @ X0)
% 1.87/2.07            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0))),
% 1.87/2.07      inference('sup+', [status(thm)], ['6', '32'])).
% 1.87/2.07  thf('34', plain,
% 1.87/2.07      (![X0 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ((k2_relat_1 @ X0)
% 1.87/2.07              = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 1.87/2.07      inference('simplify', [status(thm)], ['33'])).
% 1.87/2.07  thf('35', plain,
% 1.87/2.07      (![X9 : $i, X10 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X9)
% 1.87/2.07          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 1.87/2.07              = (k10_relat_1 @ X10 @ (k1_relat_1 @ X9)))
% 1.87/2.07          | ~ (v1_relat_1 @ X10))),
% 1.87/2.07      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.87/2.07  thf(t22_funct_1, axiom,
% 1.87/2.07    (![A:$i,B:$i]:
% 1.87/2.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.87/2.07       ( ![C:$i]:
% 1.87/2.07         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.87/2.07           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 1.87/2.07             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 1.87/2.07               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 1.87/2.07  thf('36', plain,
% 1.87/2.07      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X22)
% 1.87/2.07          | ~ (v1_funct_1 @ X22)
% 1.87/2.07          | ((k1_funct_1 @ (k5_relat_1 @ X22 @ X23) @ X24)
% 1.87/2.07              = (k1_funct_1 @ X23 @ (k1_funct_1 @ X22 @ X24)))
% 1.87/2.07          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ (k5_relat_1 @ X22 @ X23)))
% 1.87/2.07          | ~ (v1_funct_1 @ X23)
% 1.87/2.07          | ~ (v1_relat_1 @ X23))),
% 1.87/2.07      inference('cnf', [status(esa)], [t22_funct_1])).
% 1.87/2.07  thf('37', plain,
% 1.87/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.07         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 1.87/2.07          | ~ (v1_relat_1 @ X1)
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.87/2.07              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 1.87/2.07          | ~ (v1_funct_1 @ X1)
% 1.87/2.07          | ~ (v1_relat_1 @ X1))),
% 1.87/2.07      inference('sup-', [status(thm)], ['35', '36'])).
% 1.87/2.07  thf('38', plain,
% 1.87/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.07         (~ (v1_funct_1 @ X1)
% 1.87/2.07          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.87/2.07              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X1)
% 1.87/2.07          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 1.87/2.07      inference('simplify', [status(thm)], ['37'])).
% 1.87/2.07  thf('39', plain,
% 1.87/2.07      (![X0 : $i, X1 : $i]:
% 1.87/2.07         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 1.87/2.07              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 1.87/2.07          | ~ (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 1.87/2.07      inference('sup-', [status(thm)], ['34', '38'])).
% 1.87/2.07  thf('40', plain,
% 1.87/2.07      (![X0 : $i, X1 : $i]:
% 1.87/2.07         (~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 1.87/2.07          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 1.87/2.07              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 1.87/2.07      inference('simplify', [status(thm)], ['39'])).
% 1.87/2.07  thf('41', plain,
% 1.87/2.07      (![X0 : $i, X1 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ~ (v2_funct_1 @ X0)
% 1.87/2.07          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 1.87/2.07              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1))))),
% 1.87/2.07      inference('sup-', [status(thm)], ['5', '40'])).
% 1.87/2.07  thf('42', plain,
% 1.87/2.07      (![X0 : $i, X1 : $i]:
% 1.87/2.07         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 1.87/2.07            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 1.87/2.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 1.87/2.07          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.87/2.07          | ~ (v2_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0))),
% 1.87/2.07      inference('simplify', [status(thm)], ['41'])).
% 1.87/2.07  thf('43', plain,
% 1.87/2.07      (![X0 : $i, X1 : $i]:
% 1.87/2.07         (~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ~ (v2_funct_1 @ X0)
% 1.87/2.07          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.87/2.07          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 1.87/2.07              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1))))),
% 1.87/2.07      inference('sup-', [status(thm)], ['1', '42'])).
% 1.87/2.07  thf('44', plain,
% 1.87/2.07      (![X0 : $i, X1 : $i]:
% 1.87/2.07         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 1.87/2.07            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 1.87/2.07          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.87/2.07          | ~ (v2_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_funct_1 @ X0)
% 1.87/2.07          | ~ (v1_relat_1 @ X0))),
% 1.87/2.07      inference('simplify', [status(thm)], ['43'])).
% 1.87/2.07  thf('45', plain,
% 1.87/2.07      ((~ (v1_relat_1 @ sk_B)
% 1.87/2.07        | ~ (v1_funct_1 @ sk_B)
% 1.87/2.07        | ~ (v2_funct_1 @ sk_B)
% 1.87/2.07        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 1.87/2.07            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))),
% 1.87/2.07      inference('sup-', [status(thm)], ['0', '44'])).
% 1.87/2.07  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('48', plain, ((v2_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('49', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf(d5_relat_1, axiom,
% 1.87/2.07    (![A:$i,B:$i]:
% 1.87/2.07     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.87/2.07       ( ![C:$i]:
% 1.87/2.07         ( ( r2_hidden @ C @ B ) <=>
% 1.87/2.07           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.87/2.07  thf('50', plain,
% 1.87/2.07      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.87/2.07         (~ (r2_hidden @ X4 @ X3)
% 1.87/2.07          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 1.87/2.07          | ((X3) != (k2_relat_1 @ X2)))),
% 1.87/2.07      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.87/2.07  thf('51', plain,
% 1.87/2.07      (![X2 : $i, X4 : $i]:
% 1.87/2.07         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 1.87/2.07          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 1.87/2.07      inference('simplify', [status(thm)], ['50'])).
% 1.87/2.07  thf('52', plain,
% 1.87/2.07      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 1.87/2.07      inference('sup-', [status(thm)], ['49', '51'])).
% 1.87/2.07  thf(t8_funct_1, axiom,
% 1.87/2.07    (![A:$i,B:$i,C:$i]:
% 1.87/2.07     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.87/2.07       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.87/2.07         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.87/2.07           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.87/2.07  thf('53', plain,
% 1.87/2.07      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.87/2.07         (~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ X28)
% 1.87/2.07          | ((X29) = (k1_funct_1 @ X28 @ X27))
% 1.87/2.07          | ~ (v1_funct_1 @ X28)
% 1.87/2.07          | ~ (v1_relat_1 @ X28))),
% 1.87/2.07      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.87/2.07  thf('54', plain,
% 1.87/2.07      ((~ (v1_relat_1 @ sk_B)
% 1.87/2.07        | ~ (v1_funct_1 @ sk_B)
% 1.87/2.07        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))),
% 1.87/2.07      inference('sup-', [status(thm)], ['52', '53'])).
% 1.87/2.07  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('57', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 1.87/2.07      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.87/2.07  thf('58', plain,
% 1.87/2.07      (![X18 : $i]:
% 1.87/2.07         (~ (v2_funct_1 @ X18)
% 1.87/2.07          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 1.87/2.07          | ~ (v1_funct_1 @ X18)
% 1.87/2.07          | ~ (v1_relat_1 @ X18))),
% 1.87/2.07      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.87/2.07  thf('59', plain,
% 1.87/2.07      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 1.87/2.07      inference('sup-', [status(thm)], ['49', '51'])).
% 1.87/2.07  thf(t20_relat_1, axiom,
% 1.87/2.07    (![A:$i,B:$i,C:$i]:
% 1.87/2.07     ( ( v1_relat_1 @ C ) =>
% 1.87/2.07       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 1.87/2.07         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.87/2.07           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 1.87/2.07  thf('60', plain,
% 1.87/2.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.87/2.07         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13)
% 1.87/2.07          | (r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 1.87/2.07          | ~ (v1_relat_1 @ X13))),
% 1.87/2.07      inference('cnf', [status(esa)], [t20_relat_1])).
% 1.87/2.07  thf('61', plain,
% 1.87/2.07      ((~ (v1_relat_1 @ sk_B)
% 1.87/2.07        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 1.87/2.07      inference('sup-', [status(thm)], ['59', '60'])).
% 1.87/2.07  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('63', plain,
% 1.87/2.07      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 1.87/2.07      inference('demod', [status(thm)], ['61', '62'])).
% 1.87/2.07  thf(t56_funct_1, axiom,
% 1.87/2.07    (![A:$i,B:$i]:
% 1.87/2.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.87/2.07       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 1.87/2.07         ( ( ( A ) =
% 1.87/2.07             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 1.87/2.07           ( ( A ) =
% 1.87/2.07             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 1.87/2.07  thf('64', plain,
% 1.87/2.07      (![X25 : $i, X26 : $i]:
% 1.87/2.07         (~ (v2_funct_1 @ X25)
% 1.87/2.07          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X25))
% 1.87/2.07          | ((X26)
% 1.87/2.07              = (k1_funct_1 @ (k2_funct_1 @ X25) @ (k1_funct_1 @ X25 @ X26)))
% 1.87/2.07          | ~ (v1_funct_1 @ X25)
% 1.87/2.07          | ~ (v1_relat_1 @ X25))),
% 1.87/2.07      inference('cnf', [status(esa)], [t56_funct_1])).
% 1.87/2.07  thf('65', plain,
% 1.87/2.07      ((~ (v1_relat_1 @ sk_B)
% 1.87/2.07        | ~ (v1_funct_1 @ sk_B)
% 1.87/2.07        | ((sk_D_1 @ sk_A @ sk_B)
% 1.87/2.07            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 1.87/2.07               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 1.87/2.07        | ~ (v2_funct_1 @ sk_B))),
% 1.87/2.07      inference('sup-', [status(thm)], ['63', '64'])).
% 1.87/2.07  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('68', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 1.87/2.07      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.87/2.07  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('70', plain,
% 1.87/2.07      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 1.87/2.07      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 1.87/2.07  thf('71', plain,
% 1.87/2.07      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 1.87/2.07        | ~ (v1_relat_1 @ sk_B)
% 1.87/2.07        | ~ (v1_funct_1 @ sk_B)
% 1.87/2.07        | ~ (v2_funct_1 @ sk_B))),
% 1.87/2.07      inference('sup+', [status(thm)], ['58', '70'])).
% 1.87/2.07  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('74', plain, ((v2_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('75', plain,
% 1.87/2.07      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 1.87/2.07      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 1.87/2.07  thf('76', plain,
% 1.87/2.07      (((sk_A)
% 1.87/2.07         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 1.87/2.07      inference('demod', [status(thm)], ['57', '75'])).
% 1.87/2.07  thf('77', plain,
% 1.87/2.07      (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 1.87/2.07         = (sk_A))),
% 1.87/2.07      inference('demod', [status(thm)], ['45', '46', '47', '48', '76'])).
% 1.87/2.07  thf('78', plain,
% 1.87/2.07      (![X18 : $i]:
% 1.87/2.07         (~ (v2_funct_1 @ X18)
% 1.87/2.07          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 1.87/2.07          | ~ (v1_funct_1 @ X18)
% 1.87/2.07          | ~ (v1_relat_1 @ X18))),
% 1.87/2.07      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.87/2.07  thf('79', plain,
% 1.87/2.07      ((((sk_A)
% 1.87/2.07          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 1.87/2.07        | ((sk_A)
% 1.87/2.07            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('80', plain,
% 1.87/2.07      ((((sk_A)
% 1.87/2.07          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 1.87/2.07         <= (~
% 1.87/2.07             (((sk_A)
% 1.87/2.07                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.87/2.07                   sk_A))))),
% 1.87/2.07      inference('split', [status(esa)], ['79'])).
% 1.87/2.07  thf('81', plain,
% 1.87/2.07      (((((sk_A)
% 1.87/2.07           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 1.87/2.07         | ~ (v1_relat_1 @ sk_B)
% 1.87/2.07         | ~ (v1_funct_1 @ sk_B)
% 1.87/2.07         | ~ (v2_funct_1 @ sk_B)))
% 1.87/2.07         <= (~
% 1.87/2.07             (((sk_A)
% 1.87/2.07                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.87/2.07                   sk_A))))),
% 1.87/2.07      inference('sup-', [status(thm)], ['78', '80'])).
% 1.87/2.07  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('84', plain, ((v2_funct_1 @ sk_B)),
% 1.87/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.07  thf('85', plain,
% 1.87/2.07      ((((sk_A)
% 1.87/2.07          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 1.87/2.07         <= (~
% 1.87/2.07             (((sk_A)
% 1.87/2.07                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.87/2.07                   sk_A))))),
% 1.87/2.07      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 1.87/2.07  thf('86', plain,
% 1.87/2.07      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 1.87/2.07      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 1.87/2.07  thf('87', plain,
% 1.87/2.07      ((((sk_A)
% 1.87/2.07          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 1.87/2.07         <= (~
% 1.87/2.07             (((sk_A)
% 1.87/2.07                = (k1_funct_1 @ sk_B @ 
% 1.87/2.07                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 1.87/2.07      inference('split', [status(esa)], ['79'])).
% 1.87/2.07  thf('88', plain,
% 1.87/2.07      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 1.87/2.07         <= (~
% 1.87/2.07             (((sk_A)
% 1.87/2.07                = (k1_funct_1 @ sk_B @ 
% 1.87/2.07                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 1.87/2.07      inference('sup-', [status(thm)], ['86', '87'])).
% 1.87/2.07  thf('89', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 1.87/2.07      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.87/2.07  thf('90', plain,
% 1.87/2.07      ((((sk_A) != (sk_A)))
% 1.87/2.07         <= (~
% 1.87/2.07             (((sk_A)
% 1.87/2.07                = (k1_funct_1 @ sk_B @ 
% 1.87/2.07                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 1.87/2.07      inference('demod', [status(thm)], ['88', '89'])).
% 1.87/2.07  thf('91', plain,
% 1.87/2.07      ((((sk_A)
% 1.87/2.07          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 1.87/2.07      inference('simplify', [status(thm)], ['90'])).
% 1.87/2.07  thf('92', plain,
% 1.87/2.07      (~
% 1.87/2.07       (((sk_A)
% 1.87/2.07          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 1.87/2.07       ~
% 1.87/2.07       (((sk_A)
% 1.87/2.07          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 1.87/2.07      inference('split', [status(esa)], ['79'])).
% 1.87/2.07  thf('93', plain,
% 1.87/2.07      (~
% 1.87/2.07       (((sk_A)
% 1.87/2.07          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 1.87/2.07      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 1.87/2.07  thf('94', plain,
% 1.87/2.07      (((sk_A)
% 1.87/2.07         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 1.87/2.07      inference('simpl_trail', [status(thm)], ['85', '93'])).
% 1.87/2.07  thf('95', plain, ($false),
% 1.87/2.07      inference('simplify_reflect-', [status(thm)], ['77', '94'])).
% 1.87/2.07  
% 1.87/2.07  % SZS output end Refutation
% 1.87/2.07  
% 1.87/2.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
