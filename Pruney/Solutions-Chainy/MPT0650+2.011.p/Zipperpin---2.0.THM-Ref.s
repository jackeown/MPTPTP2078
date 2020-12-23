%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.raAmrOeuQC

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:20 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 233 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          : 1172 (3584 expanded)
%              Number of equality atoms :   78 ( 262 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
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

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k1_funct_1 @ X18 @ ( k1_funct_1 @ X17 @ X19 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('39',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('41',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44'])).

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

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ( X21
        = ( k1_funct_1 @ ( k2_funct_1 @ X20 ) @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('52',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','56','57'])).

thf('59',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('65',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['34','35','36','37','63','64'])).

thf('66',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('67',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','56','57'])).

thf('75',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['67'])).

thf('76',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('78',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['67'])).

thf('81',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['73','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.raAmrOeuQC
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:29:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 225 iterations in 0.203s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.46/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.65  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.46/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(t57_funct_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.46/0.65         ( ( ( A ) =
% 0.46/0.65             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.46/0.65           ( ( A ) =
% 0.46/0.65             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i]:
% 0.46/0.65        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.46/0.65            ( ( ( A ) =
% 0.46/0.65                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.46/0.65              ( ( A ) =
% 0.46/0.65                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.46/0.65  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d9_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X13 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X13)
% 0.46/0.65          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 0.46/0.65          | ~ (v1_funct_1 @ X13)
% 0.46/0.65          | ~ (v1_relat_1 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.46/0.65  thf(dt_k2_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.65         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X14 : $i]:
% 0.46/0.65         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 0.46/0.65          | ~ (v1_funct_1 @ X14)
% 0.46/0.65          | ~ (v1_relat_1 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X13 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X13)
% 0.46/0.65          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 0.46/0.65          | ~ (v1_funct_1 @ X13)
% 0.46/0.65          | ~ (v1_relat_1 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X14 : $i]:
% 0.46/0.65         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 0.46/0.65          | ~ (v1_funct_1 @ X14)
% 0.46/0.65          | ~ (v1_relat_1 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.65  thf(t37_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.46/0.65         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X2 : $i]:
% 0.46/0.65         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 0.46/0.65          | ~ (v1_relat_1 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X2 : $i]:
% 0.46/0.65         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.46/0.65          | ~ (v1_relat_1 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.46/0.65  thf(t80_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X5 : $i]:
% 0.46/0.65         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 0.46/0.65          | ~ (v1_relat_1 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.46/0.65  thf(t182_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( v1_relat_1 @ B ) =>
% 0.46/0.65           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.46/0.65             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_relat_1 @ X0)
% 0.46/0.65            = (k10_relat_1 @ X0 @ 
% 0.46/0.65               (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf(t71_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.65       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.65  thf('15', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.65  thf(fc3_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.65       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.65  thf('16', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['11', '18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65              = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.46/0.65  thf(t22_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ![C:$i]:
% 0.46/0.65         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.46/0.65             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.46/0.65               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X17)
% 0.46/0.65          | ~ (v1_funct_1 @ X17)
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ X17 @ X18) @ X19)
% 0.46/0.65              = (k1_funct_1 @ X18 @ (k1_funct_1 @ X17 @ X19)))
% 0.46/0.65          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ (k5_relat_1 @ X17 @ X18)))
% 0.46/0.65          | ~ (v1_funct_1 @ X18)
% 0.46/0.65          | ~ (v1_relat_1 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.46/0.65          | ~ (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.46/0.65          | ~ (v1_funct_1 @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ X1)
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.46/0.65          | ~ (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.46/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.46/0.65          | ~ (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.46/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '29'])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.46/0.65            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.46/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.46/0.65            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.65        | ~ (v2_funct_1 @ sk_B)
% 0.46/0.65        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.46/0.65            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '33'])).
% 0.46/0.65  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain, ((v2_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X13 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X13)
% 0.46/0.65          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 0.46/0.65          | ~ (v1_funct_1 @ X13)
% 0.46/0.65          | ~ (v1_relat_1 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.46/0.65  thf('39', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d5_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.65               ( ?[D:$i]:
% 0.46/0.65                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.46/0.65                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.46/0.65         (((X9) != (k2_relat_1 @ X7))
% 0.46/0.65          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7))
% 0.46/0.65          | ~ (r2_hidden @ X10 @ X9)
% 0.46/0.65          | ~ (v1_funct_1 @ X7)
% 0.46/0.65          | ~ (v1_relat_1 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X7 : $i, X10 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X7)
% 0.46/0.65          | ~ (v1_funct_1 @ X7)
% 0.46/0.65          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 0.46/0.65          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.46/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.65        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '41'])).
% 0.46/0.65  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.46/0.65  thf(t56_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.46/0.65         ( ( ( A ) =
% 0.46/0.65             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.46/0.65           ( ( A ) =
% 0.46/0.65             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X20)
% 0.46/0.65          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.46/0.65          | ((X21)
% 0.46/0.65              = (k1_funct_1 @ (k2_funct_1 @ X20) @ (k1_funct_1 @ X20 @ X21)))
% 0.46/0.65          | ~ (v1_funct_1 @ X20)
% 0.46/0.65          | ~ (v1_relat_1 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.65        | ((sk_D_1 @ sk_A @ sk_B)
% 0.46/0.65            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.46/0.65               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.46/0.65        | ~ (v2_funct_1 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('50', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.46/0.65         (((X9) != (k2_relat_1 @ X7))
% 0.46/0.65          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7)))
% 0.46/0.65          | ~ (r2_hidden @ X10 @ X9)
% 0.46/0.65          | ~ (v1_funct_1 @ X7)
% 0.46/0.65          | ~ (v1_relat_1 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X7 : $i, X10 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X7)
% 0.46/0.65          | ~ (v1_funct_1 @ X7)
% 0.46/0.65          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 0.46/0.65          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      ((((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))
% 0.46/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.65        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['50', '52'])).
% 0.46/0.65  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('56', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.46/0.65  thf('57', plain, ((v2_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['47', '48', '49', '56', '57'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.65        | ~ (v2_funct_1 @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['38', '58'])).
% 0.46/0.65  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('62', plain, ((v2_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.46/0.65  thf('64', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.46/0.65         = (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['34', '35', '36', '37', '63', '64'])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X13 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X13)
% 0.46/0.65          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 0.46/0.65          | ~ (v1_funct_1 @ X13)
% 0.46/0.65          | ~ (v1_relat_1 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      ((((sk_A)
% 0.46/0.65          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.46/0.65        | ((sk_A)
% 0.46/0.65            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      ((((sk_A)
% 0.46/0.65          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((sk_A)
% 0.46/0.65                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.46/0.65                   sk_A))))),
% 0.46/0.65      inference('split', [status(esa)], ['67'])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (((((sk_A)
% 0.46/0.65           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.46/0.65         | ~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | ~ (v1_funct_1 @ sk_B)
% 0.46/0.65         | ~ (v2_funct_1 @ sk_B)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((sk_A)
% 0.46/0.65                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.46/0.65                   sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['66', '68'])).
% 0.46/0.65  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('72', plain, ((v2_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      ((((sk_A)
% 0.46/0.65          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((sk_A)
% 0.46/0.65                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.46/0.65                   sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['47', '48', '49', '56', '57'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      ((((sk_A)
% 0.46/0.65          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.46/0.65         <= (~
% 0.46/0.65             (((sk_A)
% 0.46/0.65                = (k1_funct_1 @ sk_B @ 
% 0.46/0.65                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.46/0.65      inference('split', [status(esa)], ['67'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.46/0.65         <= (~
% 0.46/0.65             (((sk_A)
% 0.46/0.65                = (k1_funct_1 @ sk_B @ 
% 0.46/0.65                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.65  thf('77', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      ((((sk_A) != (sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((sk_A)
% 0.46/0.65                = (k1_funct_1 @ sk_B @ 
% 0.46/0.65                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      ((((sk_A)
% 0.46/0.65          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['78'])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (~
% 0.46/0.65       (((sk_A)
% 0.46/0.65          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.46/0.65       ~
% 0.46/0.65       (((sk_A)
% 0.46/0.65          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.46/0.65      inference('split', [status(esa)], ['67'])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      (~
% 0.46/0.65       (((sk_A)
% 0.46/0.65          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      (((sk_A)
% 0.46/0.65         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['73', '81'])).
% 0.46/0.65  thf('83', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['65', '82'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
