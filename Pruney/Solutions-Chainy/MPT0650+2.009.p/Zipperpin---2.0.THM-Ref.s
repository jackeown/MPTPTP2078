%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tDCb8DSJ6t

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:19 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  363 (1533 expanded)
%              Number of leaves         :   28 ( 457 expanded)
%              Depth                    :   64
%              Number of atoms          : 3722 (22849 expanded)
%              Number of equality atoms :  192 (1557 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('9',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('10',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k10_relat_1 @ X3 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

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
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('46',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('47',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('48',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('61',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k10_relat_1 @ X3 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

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

thf('80',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('83',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

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

thf('84',plain,(
    ! [X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( X13
       != ( k1_funct_1 @ X9 @ X14 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('85',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('96',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('98',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100','101'])).

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

thf('103',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ( X23
        = ( k1_funct_1 @ ( k2_funct_1 @ X22 ) @ ( k1_funct_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('109',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106','113','114'])).

thf('116',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['95','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('123',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','127'])).

thf('129',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('131',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('135',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','120'])).

thf('136',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('137',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['133','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('147',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('148',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('152',plain,
    ( ( ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('157',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('158',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('159',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ( X23
        = ( k1_funct_1 @ ( k2_funct_1 @ X22 ) @ ( k1_funct_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('170',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['156','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('174',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','120'])).

thf('175',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('176',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['172','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
    = ( sk_D_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['171','184','185','186','187'])).

thf('189',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','188'])).

thf('190',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('191',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k4_relat_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','191'])).

thf('193',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('194',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['192','195'])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['132','196'])).

thf('198',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','198'])).

thf('200',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['130','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['129','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['128','208','209','210'])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['79','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('216',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('218',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('219',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('220',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('221',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('223',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('225',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X1 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('226',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','120'])).

thf('227',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('228',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ( X23
        = ( k1_funct_1 @ ( k2_funct_1 @ X22 ) @ ( k1_funct_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( X1
        = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,
    ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['226','229'])).

thf('231',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['225','230'])).

thf('232',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['231','232','233'])).

thf('235',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['224','234'])).

thf('236',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['223','236'])).

thf('238',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['222','240'])).

thf('242',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['221','243'])).

thf('245',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('246',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['220','247'])).

thf('249',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['219','248'])).

thf('250',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('253',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['218','252'])).

thf('254',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','256'])).

thf('258',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['257','258','259'])).

thf('261',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['216','260'])).

thf('262',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['78','261'])).

thf('263',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','263'])).

thf('265',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['264','265','266','267'])).

thf('269',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['76','268'])).

thf('270',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['269','270'])).

thf('272',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['75','271'])).

thf('273',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('276',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('278',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['275','279'])).

thf('281',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['274','281'])).

thf('283',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['61','282'])).

thf('284',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['283','284','285'])).

thf('287',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['60','286'])).

thf('288',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['287','288','289'])).

thf('291',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','290'])).

thf('292',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('293',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('295',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','294'])).

thf('296',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    r2_hidden @ sk_A @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['295','296'])).

thf('298',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k10_relat_1 @ X3 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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

thf('299',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k1_funct_1 @ X20 @ ( k1_funct_1 @ X19 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('300',plain,(
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
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['300'])).

thf('302',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['297','301'])).

thf('303',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('306',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('307',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['302','303','304','305','306'])).

thf('308',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('309',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['309'])).

thf('311',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['308','310'])).

thf('312',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['311','312','313','314'])).

thf('316',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106','113','114'])).

thf('317',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['309'])).

thf('318',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('320',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['318','319'])).

thf('321',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['309'])).

thf('323',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['321','322'])).

thf('324',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['315','323'])).

thf('325',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['307','324'])).

thf('326',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','325'])).

thf('327',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('329',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','328'])).

thf('330',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    $false ),
    inference(demod,[status(thm)],['329','330','331','332'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tDCb8DSJ6t
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.19/2.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.19/2.38  % Solved by: fo/fo7.sh
% 2.19/2.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.19/2.38  % done 3242 iterations in 1.944s
% 2.19/2.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.19/2.38  % SZS output start Refutation
% 2.19/2.38  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.19/2.38  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.19/2.38  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.19/2.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.19/2.38  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.19/2.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.19/2.38  thf(sk_B_type, type, sk_B: $i).
% 2.19/2.38  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.19/2.38  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.19/2.38  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.19/2.38  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.19/2.38  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.19/2.38  thf(sk_A_type, type, sk_A: $i).
% 2.19/2.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.19/2.38  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.19/2.38  thf(d9_funct_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.19/2.38       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.19/2.38  thf('0', plain,
% 2.19/2.38      (![X15 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X15)
% 2.19/2.38          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 2.19/2.38          | ~ (v1_funct_1 @ X15)
% 2.19/2.38          | ~ (v1_relat_1 @ X15))),
% 2.19/2.38      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.19/2.38  thf(dt_k2_funct_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.19/2.38       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.19/2.38         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.19/2.38  thf('1', plain,
% 2.19/2.38      (![X16 : $i]:
% 2.19/2.38         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 2.19/2.38          | ~ (v1_funct_1 @ X16)
% 2.19/2.38          | ~ (v1_relat_1 @ X16))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.19/2.38  thf('2', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0))),
% 2.19/2.38      inference('sup+', [status(thm)], ['0', '1'])).
% 2.19/2.38  thf('3', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['2'])).
% 2.19/2.38  thf(dt_k4_relat_1, axiom,
% 2.19/2.38    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 2.19/2.38  thf('4', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf(t37_relat_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( v1_relat_1 @ A ) =>
% 2.19/2.38       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 2.19/2.38         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 2.19/2.38  thf('5', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf(involutiveness_k4_relat_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 2.19/2.38  thf('6', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('7', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('8', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf('9', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('10', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf(t80_relat_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( v1_relat_1 @ A ) =>
% 2.19/2.38       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.19/2.38  thf('11', plain,
% 2.19/2.38      (![X7 : $i]:
% 2.19/2.38         (((k5_relat_1 @ X7 @ (k6_relat_1 @ (k2_relat_1 @ X7))) = (X7))
% 2.19/2.38          | ~ (v1_relat_1 @ X7))),
% 2.19/2.38      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.19/2.38  thf('12', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.19/2.38            = (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup+', [status(thm)], ['10', '11'])).
% 2.19/2.38  thf('13', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('14', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.19/2.38              = (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('clc', [status(thm)], ['12', '13'])).
% 2.19/2.38  thf('15', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38            = (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup+', [status(thm)], ['9', '14'])).
% 2.19/2.38  thf('16', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('17', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38              = (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 2.19/2.38      inference('clc', [status(thm)], ['15', '16'])).
% 2.19/2.38  thf('18', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 2.19/2.38            = (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('sup+', [status(thm)], ['8', '17'])).
% 2.19/2.38  thf('19', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 2.19/2.38              = (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['18'])).
% 2.19/2.38  thf(t182_relat_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( v1_relat_1 @ A ) =>
% 2.19/2.38       ( ![B:$i]:
% 2.19/2.38         ( ( v1_relat_1 @ B ) =>
% 2.19/2.38           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.19/2.38             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.19/2.38  thf('20', plain,
% 2.19/2.38      (![X2 : $i, X3 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X2)
% 2.19/2.38          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 2.19/2.38              = (k10_relat_1 @ X3 @ (k1_relat_1 @ X2)))
% 2.19/2.38          | ~ (v1_relat_1 @ X3))),
% 2.19/2.38      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.19/2.38  thf('21', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38            = (k10_relat_1 @ X0 @ 
% 2.19/2.38               (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 2.19/2.38      inference('sup+', [status(thm)], ['19', '20'])).
% 2.19/2.38  thf(t71_relat_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.19/2.38       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.19/2.38  thf('22', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 2.19/2.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.19/2.38  thf(fc4_funct_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.19/2.38       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.19/2.38  thf('23', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 2.19/2.38      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.19/2.38  thf('24', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38            = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('demod', [status(thm)], ['21', '22', '23'])).
% 2.19/2.38  thf('25', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['24'])).
% 2.19/2.38  thf('26', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['24'])).
% 2.19/2.38  thf('27', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf('28', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38            = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup+', [status(thm)], ['26', '27'])).
% 2.19/2.38  thf('29', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('30', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 2.19/2.38      inference('clc', [status(thm)], ['28', '29'])).
% 2.19/2.38  thf('31', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38            = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('sup+', [status(thm)], ['25', '30'])).
% 2.19/2.38  thf('32', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38              = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['31'])).
% 2.19/2.38  thf('33', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf('34', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 2.19/2.38      inference('clc', [status(thm)], ['28', '29'])).
% 2.19/2.38  thf('35', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup+', [status(thm)], ['33', '34'])).
% 2.19/2.38  thf('36', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('37', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38              = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 2.19/2.38      inference('clc', [status(thm)], ['35', '36'])).
% 2.19/2.38  thf('38', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38            = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 2.19/2.38               (k2_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 2.19/2.38      inference('sup+', [status(thm)], ['32', '37'])).
% 2.19/2.38  thf('39', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ 
% 2.19/2.38              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38              = (k10_relat_1 @ 
% 2.19/2.38                 (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 2.19/2.38                 (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['7', '38'])).
% 2.19/2.38  thf('40', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38            = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 2.19/2.38               (k2_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('simplify', [status(thm)], ['39'])).
% 2.19/2.38  thf('41', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38            = (k10_relat_1 @ (k4_relat_1 @ X0) @ 
% 2.19/2.38               (k2_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('sup+', [status(thm)], ['6', '40'])).
% 2.19/2.38  thf('42', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ 
% 2.19/2.38              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38              = (k10_relat_1 @ (k4_relat_1 @ X0) @ 
% 2.19/2.38                 (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['41'])).
% 2.19/2.38  thf('43', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('sup+', [status(thm)], ['5', '42'])).
% 2.19/2.38  thf('44', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ 
% 2.19/2.38              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38              = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['43'])).
% 2.19/2.38  thf('45', plain,
% 2.19/2.38      (![X7 : $i]:
% 2.19/2.38         (((k5_relat_1 @ X7 @ (k6_relat_1 @ (k2_relat_1 @ X7))) = (X7))
% 2.19/2.38          | ~ (v1_relat_1 @ X7))),
% 2.19/2.38      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.19/2.38  thf('46', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf('47', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('48', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('49', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38              = (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 2.19/2.38      inference('clc', [status(thm)], ['15', '16'])).
% 2.19/2.38  thf('50', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.19/2.38            = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup+', [status(thm)], ['48', '49'])).
% 2.19/2.38  thf('51', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('52', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.19/2.38              = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.19/2.38      inference('clc', [status(thm)], ['50', '51'])).
% 2.19/2.38  thf('53', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38            = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup+', [status(thm)], ['47', '52'])).
% 2.19/2.38  thf('54', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('55', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38              = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))),
% 2.19/2.38      inference('clc', [status(thm)], ['53', '54'])).
% 2.19/2.38  thf('56', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 2.19/2.38            = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('sup+', [status(thm)], ['46', '55'])).
% 2.19/2.38  thf('57', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 2.19/2.38              = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['56'])).
% 2.19/2.38  thf('58', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((X0)
% 2.19/2.38            = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('sup+', [status(thm)], ['45', '57'])).
% 2.19/2.38  thf('59', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((X0)
% 2.19/2.38              = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['58'])).
% 2.19/2.38  thf('60', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('61', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('62', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38              = (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 2.19/2.38      inference('clc', [status(thm)], ['15', '16'])).
% 2.19/2.38  thf('63', plain,
% 2.19/2.38      (![X2 : $i, X3 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X2)
% 2.19/2.38          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 2.19/2.38              = (k10_relat_1 @ X3 @ (k1_relat_1 @ X2)))
% 2.19/2.38          | ~ (v1_relat_1 @ X3))),
% 2.19/2.38      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.19/2.38  thf('64', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38            = (k10_relat_1 @ X0 @ 
% 2.19/2.38               (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.19/2.38      inference('sup+', [status(thm)], ['62', '63'])).
% 2.19/2.38  thf('65', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 2.19/2.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.19/2.38  thf('66', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 2.19/2.38      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.19/2.38  thf('67', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38            = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('demod', [status(thm)], ['64', '65', '66'])).
% 2.19/2.38  thf('68', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38              = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['67'])).
% 2.19/2.38  thf('69', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('70', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38              = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 2.19/2.38      inference('clc', [status(thm)], ['35', '36'])).
% 2.19/2.38  thf('71', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38            = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup+', [status(thm)], ['69', '70'])).
% 2.19/2.38  thf('72', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('73', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38              = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.19/2.38      inference('clc', [status(thm)], ['71', '72'])).
% 2.19/2.38  thf('74', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38            = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('sup+', [status(thm)], ['68', '73'])).
% 2.19/2.38  thf('75', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38              = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['74'])).
% 2.19/2.38  thf('76', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('77', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['2'])).
% 2.19/2.38  thf('78', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('79', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf(t57_funct_1, conjecture,
% 2.19/2.38    (![A:$i,B:$i]:
% 2.19/2.38     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.19/2.38       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 2.19/2.38         ( ( ( A ) =
% 2.19/2.38             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 2.19/2.38           ( ( A ) =
% 2.19/2.38             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 2.19/2.38  thf(zf_stmt_0, negated_conjecture,
% 2.19/2.38    (~( ![A:$i,B:$i]:
% 2.19/2.38        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.19/2.38          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 2.19/2.38            ( ( ( A ) =
% 2.19/2.38                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 2.19/2.38              ( ( A ) =
% 2.19/2.38                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 2.19/2.38    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 2.19/2.38  thf('80', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('81', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('82', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['2'])).
% 2.19/2.38  thf('83', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf(d5_funct_1, axiom,
% 2.19/2.38    (![A:$i]:
% 2.19/2.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.19/2.38       ( ![B:$i]:
% 2.19/2.38         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.19/2.38           ( ![C:$i]:
% 2.19/2.38             ( ( r2_hidden @ C @ B ) <=>
% 2.19/2.38               ( ?[D:$i]:
% 2.19/2.38                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 2.19/2.38                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 2.19/2.38  thf('84', plain,
% 2.19/2.38      (![X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 2.19/2.38         (((X11) != (k2_relat_1 @ X9))
% 2.19/2.38          | (r2_hidden @ X13 @ X11)
% 2.19/2.38          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 2.19/2.38          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (v1_relat_1 @ X9))),
% 2.19/2.38      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.19/2.38  thf('85', plain,
% 2.19/2.38      (![X9 : $i, X14 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X9)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 2.19/2.38          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['84'])).
% 2.19/2.38  thf('86', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['83', '85'])).
% 2.19/2.38  thf('87', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['82', '86'])).
% 2.19/2.38  thf('88', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 2.19/2.38          | (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('simplify', [status(thm)], ['87'])).
% 2.19/2.38  thf('89', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v2_funct_1 @ X0)
% 2.19/2.38          | (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['81', '88'])).
% 2.19/2.38  thf('90', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 2.19/2.38          | (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('simplify', [status(thm)], ['89'])).
% 2.19/2.38  thf('91', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v2_funct_1 @ sk_B)
% 2.19/2.38        | (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 2.19/2.38           (k2_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['80', '90'])).
% 2.19/2.38  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('93', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('94', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('95', plain,
% 2.19/2.38      (![X15 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X15)
% 2.19/2.38          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 2.19/2.38          | ~ (v1_funct_1 @ X15)
% 2.19/2.38          | ~ (v1_relat_1 @ X15))),
% 2.19/2.38      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.19/2.38  thf('96', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('97', plain,
% 2.19/2.38      (![X9 : $i, X11 : $i, X12 : $i]:
% 2.19/2.38         (((X11) != (k2_relat_1 @ X9))
% 2.19/2.38          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 2.19/2.38          | ~ (r2_hidden @ X12 @ X11)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (v1_relat_1 @ X9))),
% 2.19/2.38      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.19/2.38  thf('98', plain,
% 2.19/2.38      (![X9 : $i, X12 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X9)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 2.19/2.38          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['97'])).
% 2.19/2.38  thf('99', plain,
% 2.19/2.38      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup-', [status(thm)], ['96', '98'])).
% 2.19/2.38  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('101', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('102', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 2.19/2.38      inference('demod', [status(thm)], ['99', '100', '101'])).
% 2.19/2.38  thf(t56_funct_1, axiom,
% 2.19/2.38    (![A:$i,B:$i]:
% 2.19/2.38     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.19/2.38       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 2.19/2.38         ( ( ( A ) =
% 2.19/2.38             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 2.19/2.38           ( ( A ) =
% 2.19/2.38             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 2.19/2.38  thf('103', plain,
% 2.19/2.38      (![X22 : $i, X23 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X22)
% 2.19/2.38          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 2.19/2.38          | ((X23)
% 2.19/2.38              = (k1_funct_1 @ (k2_funct_1 @ X22) @ (k1_funct_1 @ X22 @ X23)))
% 2.19/2.38          | ~ (v1_funct_1 @ X22)
% 2.19/2.38          | ~ (v1_relat_1 @ X22))),
% 2.19/2.38      inference('cnf', [status(esa)], [t56_funct_1])).
% 2.19/2.38  thf('104', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 2.19/2.38               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 2.19/2.38        | ~ (v2_funct_1 @ sk_B))),
% 2.19/2.38      inference('sup-', [status(thm)], ['102', '103'])).
% 2.19/2.38  thf('105', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('106', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('107', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('108', plain,
% 2.19/2.38      (![X9 : $i, X11 : $i, X12 : $i]:
% 2.19/2.38         (((X11) != (k2_relat_1 @ X9))
% 2.19/2.38          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 2.19/2.38          | ~ (r2_hidden @ X12 @ X11)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (v1_relat_1 @ X9))),
% 2.19/2.38      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.19/2.38  thf('109', plain,
% 2.19/2.38      (![X9 : $i, X12 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X9)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 2.19/2.38          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['108'])).
% 2.19/2.38  thf('110', plain,
% 2.19/2.38      ((((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup-', [status(thm)], ['107', '109'])).
% 2.19/2.38  thf('111', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('112', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('113', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.19/2.38  thf('114', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('115', plain,
% 2.19/2.38      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 2.19/2.38      inference('demod', [status(thm)], ['104', '105', '106', '113', '114'])).
% 2.19/2.38  thf('116', plain,
% 2.19/2.38      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v2_funct_1 @ sk_B))),
% 2.19/2.38      inference('sup+', [status(thm)], ['95', '115'])).
% 2.19/2.38  thf('117', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('118', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('119', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('120', plain,
% 2.19/2.38      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 2.19/2.38      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 2.19/2.38  thf('121', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['91', '92', '93', '94', '120'])).
% 2.19/2.38  thf('122', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('123', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('124', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['83', '85'])).
% 2.19/2.38  thf('125', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['123', '124'])).
% 2.19/2.38  thf('126', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0))),
% 2.19/2.38      inference('sup-', [status(thm)], ['122', '125'])).
% 2.19/2.38  thf('127', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['126'])).
% 2.19/2.38  thf('128', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38            (sk_D_1 @ sk_A @ sk_B)) @ 
% 2.19/2.38           (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B))),
% 2.19/2.38      inference('sup-', [status(thm)], ['121', '127'])).
% 2.19/2.38  thf('129', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('130', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('131', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('132', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('133', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('134', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['2'])).
% 2.19/2.38  thf('135', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['91', '92', '93', '94', '120'])).
% 2.19/2.38  thf('136', plain,
% 2.19/2.38      (![X9 : $i, X12 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X9)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 2.19/2.38          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['97'])).
% 2.19/2.38  thf('137', plain,
% 2.19/2.38      (((r2_hidden @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38         (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['135', '136'])).
% 2.19/2.38  thf('138', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v2_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38           (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['134', '137'])).
% 2.19/2.38  thf('139', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('140', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('141', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('142', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38           (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 2.19/2.38  thf('143', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38           (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['133', '142'])).
% 2.19/2.38  thf('144', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('145', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38        (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['143', '144'])).
% 2.19/2.38  thf('146', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf('147', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38        (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['143', '144'])).
% 2.19/2.38  thf('148', plain,
% 2.19/2.38      (((r2_hidden @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38         (k2_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup+', [status(thm)], ['146', '147'])).
% 2.19/2.38  thf('149', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('150', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38        (k2_relat_1 @ sk_B))),
% 2.19/2.38      inference('demod', [status(thm)], ['148', '149'])).
% 2.19/2.38  thf('151', plain,
% 2.19/2.38      (![X9 : $i, X12 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X9)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 2.19/2.38          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['108'])).
% 2.19/2.38  thf('152', plain,
% 2.19/2.38      ((((sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B))
% 2.19/2.38          = (k1_funct_1 @ sk_B @ 
% 2.19/2.38             (sk_D_1 @ 
% 2.19/2.38              (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup-', [status(thm)], ['150', '151'])).
% 2.19/2.38  thf('153', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('154', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('155', plain,
% 2.19/2.38      (((sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B))
% 2.19/2.38         = (k1_funct_1 @ sk_B @ 
% 2.19/2.38            (sk_D_1 @ 
% 2.19/2.38             (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['152', '153', '154'])).
% 2.19/2.38  thf('156', plain,
% 2.19/2.38      (![X15 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X15)
% 2.19/2.38          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 2.19/2.38          | ~ (v1_funct_1 @ X15)
% 2.19/2.38          | ~ (v1_relat_1 @ X15))),
% 2.19/2.38      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.19/2.38  thf('157', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38        (k2_relat_1 @ sk_B))),
% 2.19/2.38      inference('demod', [status(thm)], ['148', '149'])).
% 2.19/2.38  thf('158', plain,
% 2.19/2.38      (![X9 : $i, X12 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X9)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 2.19/2.38          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['97'])).
% 2.19/2.38  thf('159', plain,
% 2.19/2.38      (((r2_hidden @ 
% 2.19/2.38         (sk_D_1 @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38          sk_B) @ 
% 2.19/2.38         (k1_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup-', [status(thm)], ['157', '158'])).
% 2.19/2.38  thf('160', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('161', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('162', plain,
% 2.19/2.38      ((r2_hidden @ 
% 2.19/2.38        (sk_D_1 @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38         sk_B) @ 
% 2.19/2.38        (k1_relat_1 @ sk_B))),
% 2.19/2.38      inference('demod', [status(thm)], ['159', '160', '161'])).
% 2.19/2.38  thf('163', plain,
% 2.19/2.38      (![X22 : $i, X23 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X22)
% 2.19/2.38          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 2.19/2.38          | ((X23)
% 2.19/2.38              = (k1_funct_1 @ (k2_funct_1 @ X22) @ (k1_funct_1 @ X22 @ X23)))
% 2.19/2.38          | ~ (v1_funct_1 @ X22)
% 2.19/2.38          | ~ (v1_relat_1 @ X22))),
% 2.19/2.38      inference('cnf', [status(esa)], [t56_funct_1])).
% 2.19/2.38  thf('164', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ((sk_D_1 @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38            sk_B)
% 2.19/2.38            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 2.19/2.38               (k1_funct_1 @ sk_B @ 
% 2.19/2.38                (sk_D_1 @ 
% 2.19/2.38                 (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ sk_B))))
% 2.19/2.38        | ~ (v2_funct_1 @ sk_B))),
% 2.19/2.38      inference('sup-', [status(thm)], ['162', '163'])).
% 2.19/2.38  thf('165', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('166', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('167', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('168', plain,
% 2.19/2.38      (((sk_D_1 @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38         sk_B)
% 2.19/2.38         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 2.19/2.38            (k1_funct_1 @ sk_B @ 
% 2.19/2.38             (sk_D_1 @ 
% 2.19/2.38              (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ sk_B))))),
% 2.19/2.38      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 2.19/2.38  thf('169', plain,
% 2.19/2.38      (((sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B))
% 2.19/2.38         = (k1_funct_1 @ sk_B @ 
% 2.19/2.38            (sk_D_1 @ 
% 2.19/2.38             (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['152', '153', '154'])).
% 2.19/2.38  thf('170', plain,
% 2.19/2.38      (((sk_D_1 @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38         sk_B)
% 2.19/2.38         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 2.19/2.38            (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('demod', [status(thm)], ['168', '169'])).
% 2.19/2.38  thf('171', plain,
% 2.19/2.38      ((((sk_D_1 @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38          sk_B)
% 2.19/2.38          = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 2.19/2.38             (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B))))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v2_funct_1 @ sk_B))),
% 2.19/2.38      inference('sup+', [status(thm)], ['156', '170'])).
% 2.19/2.38  thf('172', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('173', plain,
% 2.19/2.38      (![X0 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['2'])).
% 2.19/2.38  thf('174', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['91', '92', '93', '94', '120'])).
% 2.19/2.38  thf('175', plain,
% 2.19/2.38      (![X9 : $i, X12 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X9)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 2.19/2.38          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['108'])).
% 2.19/2.38  thf('176', plain,
% 2.19/2.38      ((((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38          = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 2.19/2.38             (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B))))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['174', '175'])).
% 2.19/2.38  thf('177', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v2_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 2.19/2.38               (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['173', '176'])).
% 2.19/2.38  thf('178', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('179', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('180', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('181', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 2.19/2.38               (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)))))),
% 2.19/2.38      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 2.19/2.38  thf('182', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 2.19/2.38               (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['172', '181'])).
% 2.19/2.38  thf('183', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('184', plain,
% 2.19/2.38      (((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38         = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 2.19/2.38            (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('demod', [status(thm)], ['182', '183'])).
% 2.19/2.38  thf('185', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('186', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('187', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('188', plain,
% 2.19/2.38      (((sk_D_1 @ (sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38         sk_B) = (sk_D_1 @ sk_A @ sk_B))),
% 2.19/2.38      inference('demod', [status(thm)], ['171', '184', '185', '186', '187'])).
% 2.19/2.38  thf('189', plain,
% 2.19/2.38      (((sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B))
% 2.19/2.38         = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['155', '188'])).
% 2.19/2.38  thf('190', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.19/2.38  thf('191', plain,
% 2.19/2.38      (((sk_D_1 @ (sk_D_1 @ sk_A @ sk_B) @ (k4_relat_1 @ sk_B)) = (sk_A))),
% 2.19/2.38      inference('demod', [status(thm)], ['189', '190'])).
% 2.19/2.38  thf('192', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['145', '191'])).
% 2.19/2.38  thf('193', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf('194', plain,
% 2.19/2.38      (![X9 : $i, X12 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X9)
% 2.19/2.38          | ~ (v1_funct_1 @ X9)
% 2.19/2.38          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 2.19/2.38          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['108'])).
% 2.19/2.38  thf('195', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ((X1)
% 2.19/2.38              = (k1_funct_1 @ (k4_relat_1 @ X0) @ 
% 2.19/2.38                 (sk_D_1 @ X1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['193', '194'])).
% 2.19/2.38  thf('196', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ((sk_A)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38               (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['192', '195'])).
% 2.19/2.38  thf('197', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((sk_A)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38               (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['132', '196'])).
% 2.19/2.38  thf('198', plain,
% 2.19/2.38      ((~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ((sk_A)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38               (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['197'])).
% 2.19/2.38  thf('199', plain,
% 2.19/2.38      ((~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((sk_A)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38               (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['131', '198'])).
% 2.19/2.38  thf('200', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('201', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('202', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((sk_A)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38               (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('demod', [status(thm)], ['199', '200', '201'])).
% 2.19/2.38  thf('203', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ((sk_A)
% 2.19/2.38            = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38               (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['130', '202'])).
% 2.19/2.38  thf('204', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('205', plain,
% 2.19/2.38      (((sk_A)
% 2.19/2.38         = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38            (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 2.19/2.38      inference('demod', [status(thm)], ['203', '204'])).
% 2.19/2.38  thf('206', plain,
% 2.19/2.38      ((((sk_A)
% 2.19/2.38          = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38             (sk_D_1 @ sk_A @ sk_B)))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup+', [status(thm)], ['129', '205'])).
% 2.19/2.38  thf('207', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('208', plain,
% 2.19/2.38      (((sk_A)
% 2.19/2.38         = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38            (sk_D_1 @ sk_A @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['206', '207'])).
% 2.19/2.38  thf('209', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('210', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('211', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | (r2_hidden @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 2.19/2.38      inference('demod', [status(thm)], ['128', '208', '209', '210'])).
% 2.19/2.38  thf('212', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | (r2_hidden @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['79', '211'])).
% 2.19/2.38  thf('213', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('214', plain,
% 2.19/2.38      ((r2_hidden @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('demod', [status(thm)], ['212', '213'])).
% 2.19/2.38  thf('215', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['126'])).
% 2.19/2.38  thf('216', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38            sk_A) @ 
% 2.19/2.38           (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['214', '215'])).
% 2.19/2.38  thf('217', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('218', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('219', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('220', plain,
% 2.19/2.38      (![X15 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X15)
% 2.19/2.38          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 2.19/2.38          | ~ (v1_funct_1 @ X15)
% 2.19/2.38          | ~ (v1_relat_1 @ X15))),
% 2.19/2.38      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.19/2.38  thf('221', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('222', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('223', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('224', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('225', plain,
% 2.19/2.38      (![X1 : $i]:
% 2.19/2.38         (((k4_relat_1 @ (k4_relat_1 @ X1)) = (X1)) | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.19/2.38  thf('226', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['91', '92', '93', '94', '120'])).
% 2.19/2.38  thf('227', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf('228', plain,
% 2.19/2.38      (![X22 : $i, X23 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X22)
% 2.19/2.38          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 2.19/2.38          | ((X23)
% 2.19/2.38              = (k1_funct_1 @ (k2_funct_1 @ X22) @ (k1_funct_1 @ X22 @ X23)))
% 2.19/2.38          | ~ (v1_funct_1 @ X22)
% 2.19/2.38          | ~ (v1_relat_1 @ X22))),
% 2.19/2.38      inference('cnf', [status(esa)], [t56_funct_1])).
% 2.19/2.38  thf('229', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ((X1)
% 2.19/2.38              = (k1_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)) @ 
% 2.19/2.38                 (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 2.19/2.38          | ~ (v2_funct_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['227', '228'])).
% 2.19/2.38  thf('230', plain,
% 2.19/2.38      ((~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38               (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38                (sk_D_1 @ sk_A @ sk_B))))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['226', '229'])).
% 2.19/2.38  thf('231', plain,
% 2.19/2.38      ((~ (v2_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38               (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38                (sk_D_1 @ sk_A @ sk_B)))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['225', '230'])).
% 2.19/2.38  thf('232', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('233', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('234', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38               (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38                (sk_D_1 @ sk_A @ sk_B)))))),
% 2.19/2.38      inference('demod', [status(thm)], ['231', '232', '233'])).
% 2.19/2.38  thf('235', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38               (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38                (sk_D_1 @ sk_A @ sk_B))))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['224', '234'])).
% 2.19/2.38  thf('236', plain,
% 2.19/2.38      ((~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38               (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38                (sk_D_1 @ sk_A @ sk_B))))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['235'])).
% 2.19/2.38  thf('237', plain,
% 2.19/2.38      ((~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38               (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38                (sk_D_1 @ sk_A @ sk_B)))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['223', '236'])).
% 2.19/2.38  thf('238', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('239', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('240', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38               (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38                (sk_D_1 @ sk_A @ sk_B)))))),
% 2.19/2.38      inference('demod', [status(thm)], ['237', '238', '239'])).
% 2.19/2.38  thf('241', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38               (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38                (sk_D_1 @ sk_A @ sk_B)))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['222', '240'])).
% 2.19/2.38  thf('242', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('243', plain,
% 2.19/2.38      (((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38         = (k1_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38            (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 2.19/2.38             (sk_D_1 @ sk_A @ sk_B))))),
% 2.19/2.38      inference('demod', [status(thm)], ['241', '242'])).
% 2.19/2.38  thf('244', plain,
% 2.19/2.38      ((((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38          = (k1_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38             (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup+', [status(thm)], ['221', '243'])).
% 2.19/2.38  thf('245', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.19/2.38  thf('246', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('247', plain,
% 2.19/2.38      (((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38         = (k1_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38            sk_A))),
% 2.19/2.38      inference('demod', [status(thm)], ['244', '245', '246'])).
% 2.19/2.38  thf('248', plain,
% 2.19/2.38      ((((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38          = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38             sk_A))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('sup+', [status(thm)], ['220', '247'])).
% 2.19/2.38  thf('249', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ sk_A)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['219', '248'])).
% 2.19/2.38  thf('250', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('251', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('252', plain,
% 2.19/2.38      ((~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ sk_A)))),
% 2.19/2.38      inference('demod', [status(thm)], ['249', '250', '251'])).
% 2.19/2.38  thf('253', plain,
% 2.19/2.38      ((~ (v2_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ sk_A))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['218', '252'])).
% 2.19/2.38  thf('254', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('255', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('256', plain,
% 2.19/2.38      ((((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38          = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38             sk_A))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('demod', [status(thm)], ['253', '254', '255'])).
% 2.19/2.38  thf('257', plain,
% 2.19/2.38      ((~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38            = (k1_funct_1 @ 
% 2.19/2.38               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ sk_A)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['217', '256'])).
% 2.19/2.38  thf('258', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('259', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('260', plain,
% 2.19/2.38      (((sk_D_1 @ sk_A @ sk_B)
% 2.19/2.38         = (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 2.19/2.38            sk_A))),
% 2.19/2.38      inference('demod', [status(thm)], ['257', '258', '259'])).
% 2.19/2.38  thf('261', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38           (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['216', '260'])).
% 2.19/2.38  thf('262', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38           (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['78', '261'])).
% 2.19/2.38  thf('263', plain,
% 2.19/2.38      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38         (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['262'])).
% 2.19/2.38  thf('264', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v2_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38           (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['77', '263'])).
% 2.19/2.38  thf('265', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('266', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('267', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('268', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38           (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('demod', [status(thm)], ['264', '265', '266', '267'])).
% 2.19/2.38  thf('269', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38           (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['76', '268'])).
% 2.19/2.38  thf('270', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('271', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38        (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 2.19/2.38      inference('demod', [status(thm)], ['269', '270'])).
% 2.19/2.38  thf('272', plain,
% 2.19/2.38      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38         (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup+', [status(thm)], ['75', '271'])).
% 2.19/2.38  thf('273', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('274', plain,
% 2.19/2.38      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ 
% 2.19/2.38        (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('demod', [status(thm)], ['272', '273'])).
% 2.19/2.38  thf('275', plain,
% 2.19/2.38      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.19/2.38  thf('276', plain,
% 2.19/2.38      (![X4 : $i]:
% 2.19/2.38         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 2.19/2.38          | ~ (v1_relat_1 @ X4))),
% 2.19/2.38      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.19/2.38  thf('277', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['126'])).
% 2.19/2.38  thf('278', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0))),
% 2.19/2.38      inference('sup-', [status(thm)], ['276', '277'])).
% 2.19/2.38  thf('279', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_funct_1 @ X0)
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 2.19/2.38      inference('simplify', [status(thm)], ['278'])).
% 2.19/2.38  thf('280', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (v1_funct_1 @ X0))),
% 2.19/2.38      inference('sup-', [status(thm)], ['275', '279'])).
% 2.19/2.38  thf('281', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i]:
% 2.19/2.38         (~ (v1_funct_1 @ X0)
% 2.19/2.38          | (r2_hidden @ 
% 2.19/2.38             (k1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 2.19/2.38             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.19/2.38          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.38          | ~ (v1_relat_1 @ X0))),
% 2.19/2.38      inference('simplify', [status(thm)], ['280'])).
% 2.19/2.38  thf('282', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (k1_funct_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))) @ 
% 2.19/2.38            (sk_D_1 @ sk_A @ sk_B)) @ 
% 2.19/2.38           (k2_relat_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['274', '281'])).
% 2.19/2.38  thf('283', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (k1_funct_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))) @ 
% 2.19/2.38            (sk_D_1 @ sk_A @ sk_B)) @ 
% 2.19/2.38           (k2_relat_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['61', '282'])).
% 2.19/2.38  thf('284', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('285', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('286', plain,
% 2.19/2.38      ((~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (k1_funct_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))) @ 
% 2.19/2.38            (sk_D_1 @ sk_A @ sk_B)) @ 
% 2.19/2.38           (k2_relat_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))))),
% 2.19/2.38      inference('demod', [status(thm)], ['283', '284', '285'])).
% 2.19/2.38  thf('287', plain,
% 2.19/2.38      ((~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | (r2_hidden @ 
% 2.19/2.38           (k1_funct_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))) @ 
% 2.19/2.38            (sk_D_1 @ sk_A @ sk_B)) @ 
% 2.19/2.38           (k2_relat_1 @ 
% 2.19/2.38            (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['60', '286'])).
% 2.19/2.38  thf('288', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('289', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('290', plain,
% 2.19/2.38      ((r2_hidden @ 
% 2.19/2.38        (k1_funct_1 @ 
% 2.19/2.38         (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))) @ 
% 2.19/2.38         (sk_D_1 @ sk_A @ sk_B)) @ 
% 2.19/2.38        (k2_relat_1 @ 
% 2.19/2.38         (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('demod', [status(thm)], ['287', '288', '289'])).
% 2.19/2.38  thf('291', plain,
% 2.19/2.38      (((r2_hidden @ (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)) @ 
% 2.19/2.38         (k2_relat_1 @ 
% 2.19/2.38          (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup+', [status(thm)], ['59', '290'])).
% 2.19/2.38  thf('292', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.19/2.38  thf('293', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('294', plain,
% 2.19/2.38      ((r2_hidden @ sk_A @ 
% 2.19/2.38        (k2_relat_1 @ 
% 2.19/2.38         (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 2.19/2.38      inference('demod', [status(thm)], ['291', '292', '293'])).
% 2.19/2.38  thf('295', plain,
% 2.19/2.38      (((r2_hidden @ sk_A @ 
% 2.19/2.38         (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B))),
% 2.19/2.38      inference('sup+', [status(thm)], ['44', '294'])).
% 2.19/2.38  thf('296', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('297', plain,
% 2.19/2.38      ((r2_hidden @ sk_A @ 
% 2.19/2.38        (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['295', '296'])).
% 2.19/2.38  thf('298', plain,
% 2.19/2.38      (![X2 : $i, X3 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X2)
% 2.19/2.38          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 2.19/2.38              = (k10_relat_1 @ X3 @ (k1_relat_1 @ X2)))
% 2.19/2.38          | ~ (v1_relat_1 @ X3))),
% 2.19/2.38      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.19/2.38  thf(t22_funct_1, axiom,
% 2.19/2.38    (![A:$i,B:$i]:
% 2.19/2.38     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.19/2.38       ( ![C:$i]:
% 2.19/2.38         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.19/2.38           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 2.19/2.38             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 2.19/2.38               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 2.19/2.38  thf('299', plain,
% 2.19/2.38      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.19/2.38         (~ (v1_relat_1 @ X19)
% 2.19/2.38          | ~ (v1_funct_1 @ X19)
% 2.19/2.38          | ((k1_funct_1 @ (k5_relat_1 @ X19 @ X20) @ X21)
% 2.19/2.38              = (k1_funct_1 @ X20 @ (k1_funct_1 @ X19 @ X21)))
% 2.19/2.38          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ (k5_relat_1 @ X19 @ X20)))
% 2.19/2.38          | ~ (v1_funct_1 @ X20)
% 2.19/2.38          | ~ (v1_relat_1 @ X20))),
% 2.19/2.38      inference('cnf', [status(esa)], [t22_funct_1])).
% 2.19/2.38  thf('300', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.38         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 2.19/2.38          | ~ (v1_relat_1 @ X1)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 2.19/2.38              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 2.19/2.38          | ~ (v1_funct_1 @ X1)
% 2.19/2.38          | ~ (v1_relat_1 @ X1))),
% 2.19/2.38      inference('sup-', [status(thm)], ['298', '299'])).
% 2.19/2.38  thf('301', plain,
% 2.19/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.38         (~ (v1_funct_1 @ X1)
% 2.19/2.38          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 2.19/2.38              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 2.19/2.38          | ~ (v1_funct_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X0)
% 2.19/2.38          | ~ (v1_relat_1 @ X1)
% 2.19/2.38          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['300'])).
% 2.19/2.38  thf('302', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38        | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 2.19/2.38            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['297', '301'])).
% 2.19/2.38  thf('303', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('304', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('305', plain,
% 2.19/2.38      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 2.19/2.38      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 2.19/2.38  thf('306', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.19/2.38  thf('307', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 2.19/2.38            = (sk_A))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['302', '303', '304', '305', '306'])).
% 2.19/2.38  thf('308', plain,
% 2.19/2.38      (![X15 : $i]:
% 2.19/2.38         (~ (v2_funct_1 @ X15)
% 2.19/2.38          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 2.19/2.38          | ~ (v1_funct_1 @ X15)
% 2.19/2.38          | ~ (v1_relat_1 @ X15))),
% 2.19/2.38      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.19/2.38  thf('309', plain,
% 2.19/2.38      ((((sk_A)
% 2.19/2.38          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 2.19/2.38        | ((sk_A)
% 2.19/2.38            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('310', plain,
% 2.19/2.38      ((((sk_A)
% 2.19/2.38          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 2.19/2.38         <= (~
% 2.19/2.38             (((sk_A)
% 2.19/2.38                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 2.19/2.38                   sk_A))))),
% 2.19/2.38      inference('split', [status(esa)], ['309'])).
% 2.19/2.38  thf('311', plain,
% 2.19/2.38      (((((sk_A)
% 2.19/2.38           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 2.19/2.38         | ~ (v1_relat_1 @ sk_B)
% 2.19/2.38         | ~ (v1_funct_1 @ sk_B)
% 2.19/2.38         | ~ (v2_funct_1 @ sk_B)))
% 2.19/2.38         <= (~
% 2.19/2.38             (((sk_A)
% 2.19/2.38                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 2.19/2.38                   sk_A))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['308', '310'])).
% 2.19/2.38  thf('312', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('313', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('314', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('315', plain,
% 2.19/2.38      ((((sk_A)
% 2.19/2.38          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 2.19/2.38         <= (~
% 2.19/2.38             (((sk_A)
% 2.19/2.38                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 2.19/2.38                   sk_A))))),
% 2.19/2.38      inference('demod', [status(thm)], ['311', '312', '313', '314'])).
% 2.19/2.38  thf('316', plain,
% 2.19/2.38      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 2.19/2.38      inference('demod', [status(thm)], ['104', '105', '106', '113', '114'])).
% 2.19/2.38  thf('317', plain,
% 2.19/2.38      ((((sk_A)
% 2.19/2.38          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 2.19/2.38         <= (~
% 2.19/2.38             (((sk_A)
% 2.19/2.38                = (k1_funct_1 @ sk_B @ 
% 2.19/2.38                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 2.19/2.38      inference('split', [status(esa)], ['309'])).
% 2.19/2.38  thf('318', plain,
% 2.19/2.38      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 2.19/2.38         <= (~
% 2.19/2.38             (((sk_A)
% 2.19/2.38                = (k1_funct_1 @ sk_B @ 
% 2.19/2.38                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 2.19/2.38      inference('sup-', [status(thm)], ['316', '317'])).
% 2.19/2.38  thf('319', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 2.19/2.38      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.19/2.38  thf('320', plain,
% 2.19/2.38      ((((sk_A) != (sk_A)))
% 2.19/2.38         <= (~
% 2.19/2.38             (((sk_A)
% 2.19/2.38                = (k1_funct_1 @ sk_B @ 
% 2.19/2.38                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 2.19/2.38      inference('demod', [status(thm)], ['318', '319'])).
% 2.19/2.38  thf('321', plain,
% 2.19/2.38      ((((sk_A)
% 2.19/2.38          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 2.19/2.38      inference('simplify', [status(thm)], ['320'])).
% 2.19/2.38  thf('322', plain,
% 2.19/2.38      (~
% 2.19/2.38       (((sk_A)
% 2.19/2.38          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 2.19/2.38       ~
% 2.19/2.38       (((sk_A)
% 2.19/2.38          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 2.19/2.38      inference('split', [status(esa)], ['309'])).
% 2.19/2.38  thf('323', plain,
% 2.19/2.38      (~
% 2.19/2.38       (((sk_A)
% 2.19/2.38          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 2.19/2.38      inference('sat_resolution*', [status(thm)], ['321', '322'])).
% 2.19/2.38  thf('324', plain,
% 2.19/2.38      (((sk_A)
% 2.19/2.38         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 2.19/2.38      inference('simpl_trail', [status(thm)], ['315', '323'])).
% 2.19/2.38  thf('325', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 2.19/2.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('simplify_reflect-', [status(thm)], ['307', '324'])).
% 2.19/2.38  thf('326', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 2.19/2.38      inference('sup-', [status(thm)], ['4', '325'])).
% 2.19/2.38  thf('327', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('328', plain, (~ (v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 2.19/2.38      inference('demod', [status(thm)], ['326', '327'])).
% 2.19/2.38  thf('329', plain,
% 2.19/2.38      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 2.19/2.38      inference('sup-', [status(thm)], ['3', '328'])).
% 2.19/2.38  thf('330', plain, ((v1_relat_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('331', plain, ((v1_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('332', plain, ((v2_funct_1 @ sk_B)),
% 2.19/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.38  thf('333', plain, ($false),
% 2.19/2.38      inference('demod', [status(thm)], ['329', '330', '331', '332'])).
% 2.19/2.38  
% 2.19/2.38  % SZS output end Refutation
% 2.19/2.38  
% 2.19/2.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
