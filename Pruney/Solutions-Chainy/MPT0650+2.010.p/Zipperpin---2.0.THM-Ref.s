%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ENghWHHDeM

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:20 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 240 expanded)
%              Number of leaves         :   26 (  78 expanded)
%              Depth                    :   19
%              Number of atoms          : 1231 (3655 expanded)
%              Number of equality atoms :   83 ( 267 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','17'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
       != ( k6_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('20',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X15 @ X16 ) @ X17 )
        = ( k1_funct_1 @ X16 @ ( k1_funct_1 @ X15 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('29',plain,(
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
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
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
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
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
    inference('sup-',[status(thm)],['9','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
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
    inference('sup-',[status(thm)],['8','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['4','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('46',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

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

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ( X22
        = ( k1_funct_1 @ ( k2_funct_1 @ X21 ) @ ( k1_funct_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('57',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','61','62'])).

thf('64',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('70',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['39','40','41','42','68','69'])).

thf('71',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('72',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','61','62'])).

thf('80',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['72'])).

thf('81',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('83',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['72'])).

thf('86',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['78','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ENghWHHDeM
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:07:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.67  % Solved by: fo/fo7.sh
% 0.51/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.67  % done 188 iterations in 0.217s
% 0.51/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.67  % SZS output start Refutation
% 0.51/0.67  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.51/0.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.51/0.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.51/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.51/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.67  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.51/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.51/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.51/0.67  thf(t57_funct_1, conjecture,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.51/0.67         ( ( ( A ) =
% 0.51/0.67             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.51/0.67           ( ( A ) =
% 0.51/0.67             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.51/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.67    (~( ![A:$i,B:$i]:
% 0.51/0.67        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.51/0.67            ( ( ( A ) =
% 0.51/0.67                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.51/0.67              ( ( A ) =
% 0.51/0.67                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.51/0.67    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.51/0.67  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf(d9_funct_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.67       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.51/0.67  thf('1', plain,
% 0.51/0.67      (![X11 : $i]:
% 0.51/0.67         (~ (v2_funct_1 @ X11)
% 0.51/0.67          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.51/0.67          | ~ (v1_funct_1 @ X11)
% 0.51/0.67          | ~ (v1_relat_1 @ X11))),
% 0.51/0.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.51/0.67  thf(dt_k2_funct_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.67       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.51/0.67         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.51/0.67  thf('2', plain,
% 0.51/0.67      (![X12 : $i]:
% 0.51/0.67         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.51/0.67          | ~ (v1_funct_1 @ X12)
% 0.51/0.67          | ~ (v1_relat_1 @ X12))),
% 0.51/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.51/0.67  thf('3', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((v1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0))),
% 0.51/0.67      inference('sup+', [status(thm)], ['1', '2'])).
% 0.51/0.67  thf('4', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.51/0.67      inference('simplify', [status(thm)], ['3'])).
% 0.51/0.67  thf('5', plain,
% 0.51/0.67      (![X11 : $i]:
% 0.51/0.67         (~ (v2_funct_1 @ X11)
% 0.51/0.67          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.51/0.67          | ~ (v1_funct_1 @ X11)
% 0.51/0.67          | ~ (v1_relat_1 @ X11))),
% 0.51/0.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.51/0.67  thf('6', plain,
% 0.51/0.67      (![X12 : $i]:
% 0.51/0.67         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.51/0.67          | ~ (v1_funct_1 @ X12)
% 0.51/0.67          | ~ (v1_relat_1 @ X12))),
% 0.51/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.51/0.67  thf('7', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0))),
% 0.51/0.67      inference('sup+', [status(thm)], ['5', '6'])).
% 0.51/0.67  thf('8', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.51/0.67      inference('simplify', [status(thm)], ['7'])).
% 0.51/0.67  thf(t37_relat_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( v1_relat_1 @ A ) =>
% 0.51/0.67       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.51/0.67         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.51/0.67  thf('9', plain,
% 0.51/0.67      (![X2 : $i]:
% 0.51/0.67         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 0.51/0.67          | ~ (v1_relat_1 @ X2))),
% 0.51/0.67      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.51/0.67  thf('10', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.51/0.67      inference('simplify', [status(thm)], ['3'])).
% 0.51/0.67  thf('11', plain,
% 0.51/0.67      (![X2 : $i]:
% 0.51/0.67         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.51/0.67          | ~ (v1_relat_1 @ X2))),
% 0.51/0.67      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.51/0.67  thf(t80_relat_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( v1_relat_1 @ A ) =>
% 0.51/0.67       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.51/0.67  thf('12', plain,
% 0.51/0.67      (![X3 : $i]:
% 0.51/0.67         (((k5_relat_1 @ X3 @ (k6_relat_1 @ (k2_relat_1 @ X3))) = (X3))
% 0.51/0.67          | ~ (v1_relat_1 @ X3))),
% 0.51/0.67      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.51/0.67  thf(t182_relat_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( v1_relat_1 @ A ) =>
% 0.51/0.67       ( ![B:$i]:
% 0.51/0.67         ( ( v1_relat_1 @ B ) =>
% 0.51/0.67           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.51/0.67             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.51/0.67  thf('13', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.51/0.67              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.51/0.67          | ~ (v1_relat_1 @ X1))),
% 0.51/0.67      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.51/0.67  thf('14', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (((k1_relat_1 @ X0)
% 0.51/0.67            = (k10_relat_1 @ X0 @ 
% 0.51/0.67               (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.51/0.67      inference('sup+', [status(thm)], ['12', '13'])).
% 0.51/0.67  thf(fc3_funct_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.51/0.67       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.51/0.67  thf('15', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.51/0.67      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.67  thf('16', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (((k1_relat_1 @ X0)
% 0.51/0.67            = (k10_relat_1 @ X0 @ 
% 0.51/0.67               (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0))),
% 0.51/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.67  thf('17', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | ((k1_relat_1 @ X0)
% 0.51/0.67              = (k10_relat_1 @ X0 @ 
% 0.51/0.67                 (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['16'])).
% 0.51/0.67  thf('18', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67            = (k10_relat_1 @ (k4_relat_1 @ X0) @ 
% 0.51/0.67               (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.51/0.67      inference('sup+', [status(thm)], ['11', '17'])).
% 0.51/0.67  thf(t34_funct_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.51/0.67         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.51/0.67           ( ![C:$i]:
% 0.51/0.67             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.51/0.67  thf('19', plain,
% 0.51/0.67      (![X18 : $i, X19 : $i]:
% 0.51/0.67         (((X19) != (k6_relat_1 @ X18))
% 0.51/0.67          | ((k1_relat_1 @ X19) = (X18))
% 0.51/0.67          | ~ (v1_funct_1 @ X19)
% 0.51/0.67          | ~ (v1_relat_1 @ X19))),
% 0.51/0.67      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.51/0.67  thf('20', plain,
% 0.51/0.67      (![X18 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ (k6_relat_1 @ X18))
% 0.51/0.67          | ~ (v1_funct_1 @ (k6_relat_1 @ X18))
% 0.51/0.67          | ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18)))),
% 0.51/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.51/0.67  thf('21', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.51/0.67      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.67  thf('22', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.51/0.67      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.67  thf('23', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.51/0.67      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.51/0.67  thf('24', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.51/0.67      inference('demod', [status(thm)], ['18', '23'])).
% 0.51/0.67  thf('25', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67              = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['10', '24'])).
% 0.51/0.67  thf('26', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0))),
% 0.51/0.67      inference('simplify', [status(thm)], ['25'])).
% 0.51/0.67  thf('27', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.51/0.67              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.51/0.67          | ~ (v1_relat_1 @ X1))),
% 0.51/0.67      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.51/0.67  thf(t22_funct_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67       ( ![C:$i]:
% 0.51/0.67         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.67           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.51/0.67             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.51/0.67               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.51/0.67  thf('28', plain,
% 0.51/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X15)
% 0.51/0.67          | ~ (v1_funct_1 @ X15)
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ X15 @ X16) @ X17)
% 0.51/0.67              = (k1_funct_1 @ X16 @ (k1_funct_1 @ X15 @ X17)))
% 0.51/0.67          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X16)))
% 0.51/0.67          | ~ (v1_funct_1 @ X16)
% 0.51/0.67          | ~ (v1_relat_1 @ X16))),
% 0.51/0.67      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.51/0.67  thf('29', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.67         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.51/0.67          | ~ (v1_relat_1 @ X1)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.51/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.51/0.67          | ~ (v1_funct_1 @ X1)
% 0.51/0.67          | ~ (v1_relat_1 @ X1))),
% 0.51/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.67  thf('30', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.67         (~ (v1_funct_1 @ X1)
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.51/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X1)
% 0.51/0.67          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['29'])).
% 0.51/0.67  thf('31', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.51/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.51/0.67          | ~ (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['26', '30'])).
% 0.51/0.67  thf('32', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.51/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.51/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['31'])).
% 0.51/0.67  thf('33', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.51/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.51/0.67          | ~ (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['9', '32'])).
% 0.51/0.67  thf('34', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.51/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.51/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.51/0.67      inference('simplify', [status(thm)], ['33'])).
% 0.51/0.67  thf('35', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.51/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['8', '34'])).
% 0.51/0.67  thf('36', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.51/0.67            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.51/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.51/0.67          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0))),
% 0.51/0.67      inference('simplify', [status(thm)], ['35'])).
% 0.51/0.67  thf('37', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.51/0.67          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.51/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['4', '36'])).
% 0.51/0.67  thf('38', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.51/0.67            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.51/0.67          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.51/0.67          | ~ (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0))),
% 0.51/0.67      inference('simplify', [status(thm)], ['37'])).
% 0.51/0.67  thf('39', plain,
% 0.51/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.51/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67        | ~ (v2_funct_1 @ sk_B)
% 0.51/0.67        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.51/0.67            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['0', '38'])).
% 0.51/0.67  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('42', plain, ((v2_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('43', plain,
% 0.51/0.67      (![X11 : $i]:
% 0.51/0.67         (~ (v2_funct_1 @ X11)
% 0.51/0.67          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.51/0.67          | ~ (v1_funct_1 @ X11)
% 0.51/0.67          | ~ (v1_relat_1 @ X11))),
% 0.51/0.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.51/0.67  thf('44', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf(d5_funct_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.67       ( ![B:$i]:
% 0.51/0.67         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.51/0.67           ( ![C:$i]:
% 0.51/0.67             ( ( r2_hidden @ C @ B ) <=>
% 0.51/0.67               ( ?[D:$i]:
% 0.51/0.67                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.51/0.67                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.51/0.67  thf('45', plain,
% 0.51/0.67      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.51/0.67         (((X7) != (k2_relat_1 @ X5))
% 0.51/0.67          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 0.51/0.67          | ~ (r2_hidden @ X8 @ X7)
% 0.51/0.67          | ~ (v1_funct_1 @ X5)
% 0.51/0.67          | ~ (v1_relat_1 @ X5))),
% 0.51/0.67      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.67  thf('46', plain,
% 0.51/0.67      (![X5 : $i, X8 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X5)
% 0.51/0.67          | ~ (v1_funct_1 @ X5)
% 0.51/0.67          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 0.51/0.67          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 0.51/0.67      inference('simplify', [status(thm)], ['45'])).
% 0.51/0.67  thf('47', plain,
% 0.51/0.67      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.51/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.67      inference('sup-', [status(thm)], ['44', '46'])).
% 0.51/0.67  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('50', plain,
% 0.51/0.67      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.51/0.67      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.51/0.67  thf(t56_funct_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.51/0.67         ( ( ( A ) =
% 0.51/0.67             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.51/0.67           ( ( A ) =
% 0.51/0.67             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.51/0.67  thf('51', plain,
% 0.51/0.67      (![X21 : $i, X22 : $i]:
% 0.51/0.67         (~ (v2_funct_1 @ X21)
% 0.51/0.67          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.51/0.67          | ((X22)
% 0.51/0.67              = (k1_funct_1 @ (k2_funct_1 @ X21) @ (k1_funct_1 @ X21 @ X22)))
% 0.51/0.67          | ~ (v1_funct_1 @ X21)
% 0.51/0.67          | ~ (v1_relat_1 @ X21))),
% 0.51/0.67      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.51/0.67  thf('52', plain,
% 0.51/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.51/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67        | ((sk_D_1 @ sk_A @ sk_B)
% 0.51/0.67            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.51/0.67               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.51/0.67        | ~ (v2_funct_1 @ sk_B))),
% 0.51/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.51/0.67  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('55', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('56', plain,
% 0.51/0.67      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.51/0.67         (((X7) != (k2_relat_1 @ X5))
% 0.51/0.67          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 0.51/0.67          | ~ (r2_hidden @ X8 @ X7)
% 0.51/0.67          | ~ (v1_funct_1 @ X5)
% 0.51/0.67          | ~ (v1_relat_1 @ X5))),
% 0.51/0.67      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.67  thf('57', plain,
% 0.51/0.67      (![X5 : $i, X8 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X5)
% 0.51/0.67          | ~ (v1_funct_1 @ X5)
% 0.51/0.67          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 0.51/0.67          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['56'])).
% 0.51/0.67  thf('58', plain,
% 0.51/0.67      ((((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))
% 0.51/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.67      inference('sup-', [status(thm)], ['55', '57'])).
% 0.51/0.67  thf('59', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('61', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.51/0.67      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.51/0.67  thf('62', plain, ((v2_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('63', plain,
% 0.51/0.67      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.51/0.67      inference('demod', [status(thm)], ['52', '53', '54', '61', '62'])).
% 0.51/0.67  thf('64', plain,
% 0.51/0.67      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.51/0.67        | ~ (v1_relat_1 @ sk_B)
% 0.51/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67        | ~ (v2_funct_1 @ sk_B))),
% 0.51/0.67      inference('sup+', [status(thm)], ['43', '63'])).
% 0.51/0.67  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('67', plain, ((v2_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('68', plain,
% 0.51/0.67      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.51/0.67      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.51/0.67  thf('69', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.51/0.67      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.51/0.67  thf('70', plain,
% 0.51/0.67      (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.51/0.67         = (sk_A))),
% 0.51/0.67      inference('demod', [status(thm)], ['39', '40', '41', '42', '68', '69'])).
% 0.51/0.67  thf('71', plain,
% 0.51/0.67      (![X11 : $i]:
% 0.51/0.67         (~ (v2_funct_1 @ X11)
% 0.51/0.67          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.51/0.67          | ~ (v1_funct_1 @ X11)
% 0.51/0.67          | ~ (v1_relat_1 @ X11))),
% 0.51/0.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.51/0.67  thf('72', plain,
% 0.51/0.67      ((((sk_A)
% 0.51/0.67          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.51/0.67        | ((sk_A)
% 0.51/0.67            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('73', plain,
% 0.51/0.67      ((((sk_A)
% 0.51/0.67          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.51/0.67         <= (~
% 0.51/0.67             (((sk_A)
% 0.51/0.67                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.51/0.67                   sk_A))))),
% 0.51/0.67      inference('split', [status(esa)], ['72'])).
% 0.51/0.67  thf('74', plain,
% 0.51/0.67      (((((sk_A)
% 0.51/0.67           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.51/0.67         | ~ (v1_relat_1 @ sk_B)
% 0.51/0.67         | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67         | ~ (v2_funct_1 @ sk_B)))
% 0.51/0.67         <= (~
% 0.51/0.67             (((sk_A)
% 0.51/0.67                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.51/0.67                   sk_A))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['71', '73'])).
% 0.51/0.67  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('77', plain, ((v2_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('78', plain,
% 0.51/0.67      ((((sk_A)
% 0.51/0.67          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.51/0.67         <= (~
% 0.51/0.67             (((sk_A)
% 0.51/0.67                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.51/0.67                   sk_A))))),
% 0.51/0.67      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.51/0.67  thf('79', plain,
% 0.51/0.67      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.51/0.67      inference('demod', [status(thm)], ['52', '53', '54', '61', '62'])).
% 0.51/0.67  thf('80', plain,
% 0.51/0.67      ((((sk_A)
% 0.51/0.67          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.51/0.67         <= (~
% 0.51/0.67             (((sk_A)
% 0.51/0.67                = (k1_funct_1 @ sk_B @ 
% 0.51/0.67                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.51/0.67      inference('split', [status(esa)], ['72'])).
% 0.51/0.67  thf('81', plain,
% 0.51/0.67      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.51/0.67         <= (~
% 0.51/0.67             (((sk_A)
% 0.51/0.67                = (k1_funct_1 @ sk_B @ 
% 0.51/0.67                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['79', '80'])).
% 0.51/0.67  thf('82', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.51/0.67      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.51/0.67  thf('83', plain,
% 0.51/0.67      ((((sk_A) != (sk_A)))
% 0.51/0.67         <= (~
% 0.51/0.67             (((sk_A)
% 0.51/0.67                = (k1_funct_1 @ sk_B @ 
% 0.51/0.67                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.51/0.67      inference('demod', [status(thm)], ['81', '82'])).
% 0.51/0.67  thf('84', plain,
% 0.51/0.67      ((((sk_A)
% 0.51/0.67          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['83'])).
% 0.51/0.67  thf('85', plain,
% 0.51/0.67      (~
% 0.51/0.67       (((sk_A)
% 0.51/0.67          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.51/0.67       ~
% 0.51/0.67       (((sk_A)
% 0.51/0.67          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.51/0.67      inference('split', [status(esa)], ['72'])).
% 0.51/0.67  thf('86', plain,
% 0.51/0.67      (~
% 0.51/0.67       (((sk_A)
% 0.51/0.67          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.51/0.67      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.51/0.67  thf('87', plain,
% 0.51/0.67      (((sk_A)
% 0.51/0.67         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.51/0.67      inference('simpl_trail', [status(thm)], ['78', '86'])).
% 0.51/0.67  thf('88', plain, ($false),
% 0.51/0.67      inference('simplify_reflect-', [status(thm)], ['70', '87'])).
% 0.51/0.67  
% 0.51/0.67  % SZS output end Refutation
% 0.51/0.67  
% 0.51/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
