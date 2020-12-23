%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVwPOE0vHG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:24 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 204 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :   30
%              Number of atoms          : 1224 (2300 expanded)
%              Number of equality atoms :   88 ( 184 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('3',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ X11 @ ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('15',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('25',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) )
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) @ X0 ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) @ X0 ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t58_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
              = ( k1_relat_1 @ A ) )
            & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
              = ( k1_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_funct_1])).

thf('66',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('69',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('73',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['66'])).

thf('74',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['66'])).

thf('94',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['67','94'])).

thf('96',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    $false ),
    inference(simplify,[status(thm)],['100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVwPOE0vHG
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 223 iterations in 0.204s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.47/0.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(dt_k2_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.67         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (![X13 : $i]:
% 0.47/0.67         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.47/0.67          | ~ (v1_funct_1 @ X13)
% 0.47/0.67          | ~ (v1_relat_1 @ X13))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (![X13 : $i]:
% 0.47/0.67         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.47/0.67          | ~ (v1_funct_1 @ X13)
% 0.47/0.67          | ~ (v1_relat_1 @ X13))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.67  thf(t37_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.47/0.67         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (![X4 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.67          | ~ (v1_relat_1 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (![X13 : $i]:
% 0.47/0.67         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.47/0.67          | ~ (v1_funct_1 @ X13)
% 0.47/0.67          | ~ (v1_relat_1 @ X13))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.67  thf(t55_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ( v2_funct_1 @ A ) =>
% 0.47/0.67         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.47/0.67           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X16 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X16)
% 0.47/0.67          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 0.47/0.67          | ~ (v1_funct_1 @ X16)
% 0.47/0.67          | ~ (v1_relat_1 @ X16))),
% 0.47/0.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.47/0.67  thf(t71_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.67       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.67  thf('5', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.47/0.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.67  thf(t80_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X11 : $i]:
% 0.47/0.67         (((k5_relat_1 @ X11 @ (k6_relat_1 @ (k2_relat_1 @ X11))) = (X11))
% 0.47/0.67          | ~ (v1_relat_1 @ X11))),
% 0.47/0.67      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.47/0.67            = (k6_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['5', '6'])).
% 0.47/0.67  thf(fc4_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.67       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.67  thf('8', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.47/0.67           = (k6_relat_1 @ X0))),
% 0.47/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.67  thf(t45_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( v1_relat_1 @ B ) =>
% 0.47/0.67           ( r1_tarski @
% 0.47/0.67             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X5)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.47/0.67             (k2_relat_1 @ X5))
% 0.47/0.67          | ~ (v1_relat_1 @ X6))),
% 0.47/0.67      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.47/0.67           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.67  thf('12', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.47/0.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.67  thf('13', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.47/0.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.67  thf('14', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.67  thf('15', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.67  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.67      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.47/0.67  thf('17', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.47/0.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.67  thf(t46_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( v1_relat_1 @ B ) =>
% 0.47/0.67           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.67             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X7 : $i, X8 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X7)
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7)) = (k1_relat_1 @ X8))
% 0.47/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X8) @ (k1_relat_1 @ X7))
% 0.47/0.67          | ~ (v1_relat_1 @ X8))),
% 0.47/0.67      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.47/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.47/0.67              = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('20', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.67  thf('21', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X0))
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 0.47/0.67              = (k1_relat_1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['16', '22'])).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (![X4 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.67          | ~ (v1_relat_1 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      (![X4 : $i]:
% 0.47/0.67         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.67          | ~ (v1_relat_1 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.67  thf(t146_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      (![X1 : $i]:
% 0.47/0.67         (((k9_relat_1 @ X1 @ (k1_relat_1 @ X1)) = (k2_relat_1 @ X1))
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.67            = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['25', '26'])).
% 0.47/0.67  thf(dt_k4_relat_1, axiom,
% 0.47/0.67    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ((k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.67              = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.47/0.67      inference('clc', [status(thm)], ['27', '28'])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      (![X4 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.67          | ~ (v1_relat_1 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.67  thf('31', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.47/0.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.67  thf(t160_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( v1_relat_1 @ B ) =>
% 0.47/0.67           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.47/0.67             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      (![X2 : $i, X3 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X2)
% 0.47/0.67          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.47/0.67              = (k9_relat_1 @ X2 @ (k2_relat_1 @ X3)))
% 0.47/0.67          | ~ (v1_relat_1 @ X3))),
% 0.47/0.67      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X5)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.47/0.67             (k2_relat_1 @ X5))
% 0.47/0.67          | ~ (v1_relat_1 @ X6))),
% 0.47/0.67      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ 
% 0.47/0.67           (k2_relat_1 @ X1))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['32', '33'])).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ 
% 0.47/0.67             (k2_relat_1 @ X1)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.47/0.67          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['31', '35'])).
% 0.47/0.67  thf('37', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ (k9_relat_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 0.47/0.67           (k1_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['30', '38'])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k9_relat_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 0.47/0.67             (k1_relat_1 @ X0)))),
% 0.47/0.67      inference('clc', [status(thm)], ['39', '40'])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X0))
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ((k1_relat_1 @ 
% 0.47/0.67              (k5_relat_1 @ 
% 0.47/0.67               (k6_relat_1 @ (k9_relat_1 @ (k4_relat_1 @ X0) @ X1)) @ X0))
% 0.47/0.67              = (k9_relat_1 @ (k4_relat_1 @ X0) @ X1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((k1_relat_1 @ 
% 0.47/0.67            (k5_relat_1 @ 
% 0.47/0.67             (k6_relat_1 @ (k9_relat_1 @ (k4_relat_1 @ X0) @ X1)) @ X0))
% 0.47/0.67            = (k9_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['43'])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k1_relat_1 @ 
% 0.47/0.67            (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))) @ X0))
% 0.47/0.67            = (k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['29', '44'])).
% 0.47/0.67  thf('46', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ((k1_relat_1 @ 
% 0.47/0.67              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))) @ 
% 0.47/0.67               X0))
% 0.47/0.67              = (k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['45'])).
% 0.47/0.67  thf('47', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 0.47/0.67            = (k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['24', '46'])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 0.47/0.67              = (k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X0)
% 0.47/0.67            = (k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['23', '48'])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ((k1_relat_1 @ X0)
% 0.47/0.67              = (k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['49'])).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['50', '51'])).
% 0.47/0.67  thf('53', plain,
% 0.47/0.67      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.47/0.67  thf('54', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.47/0.67      inference('clc', [status(thm)], ['52', '53'])).
% 0.47/0.67  thf('55', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.47/0.67           (k2_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['4', '54'])).
% 0.47/0.67  thf('56', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.47/0.67             (k2_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['3', '55'])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.47/0.67           (k2_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['56'])).
% 0.47/0.67  thf('58', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['2', '57'])).
% 0.47/0.67  thf('59', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['1', '58'])).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['59'])).
% 0.47/0.67  thf('61', plain,
% 0.47/0.67      (![X7 : $i, X8 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X7)
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7)) = (k1_relat_1 @ X8))
% 0.47/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X8) @ (k1_relat_1 @ X7))
% 0.47/0.67          | ~ (v1_relat_1 @ X8))),
% 0.47/0.67      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.47/0.67  thf('62', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.47/0.67              = (k1_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.67  thf('63', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.47/0.67              = (k1_relat_1 @ X0))
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.47/0.67              = (k1_relat_1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['0', '63'])).
% 0.47/0.67  thf('65', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.47/0.67            = (k1_relat_1 @ X0))
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['64'])).
% 0.47/0.67  thf(t58_funct_1, conjecture,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ( v2_funct_1 @ A ) =>
% 0.47/0.67         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.47/0.67             ( k1_relat_1 @ A ) ) & 
% 0.47/0.67           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.47/0.67             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i]:
% 0.47/0.67        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67          ( ( v2_funct_1 @ A ) =>
% 0.47/0.67            ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.47/0.67                ( k1_relat_1 @ A ) ) & 
% 0.47/0.67              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.47/0.67                ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t58_funct_1])).
% 0.47/0.67  thf('66', plain,
% 0.47/0.67      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67          != (k1_relat_1 @ sk_A))
% 0.47/0.67        | ((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67            != (k1_relat_1 @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('67', plain,
% 0.47/0.67      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67          != (k1_relat_1 @ sk_A)))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('split', [status(esa)], ['66'])).
% 0.47/0.67  thf('68', plain,
% 0.47/0.67      (![X4 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.67          | ~ (v1_relat_1 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.67  thf('69', plain,
% 0.47/0.67      (![X13 : $i]:
% 0.47/0.67         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.47/0.67          | ~ (v1_funct_1 @ X13)
% 0.47/0.67          | ~ (v1_relat_1 @ X13))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.67  thf('70', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ((k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.67              = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.47/0.67      inference('clc', [status(thm)], ['27', '28'])).
% 0.47/0.67  thf(d9_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.47/0.67  thf('71', plain,
% 0.47/0.67      (![X12 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X12)
% 0.47/0.67          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.47/0.67          | ~ (v1_funct_1 @ X12)
% 0.47/0.67          | ~ (v1_relat_1 @ X12))),
% 0.47/0.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.47/0.67  thf('72', plain,
% 0.47/0.67      (![X2 : $i, X3 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X2)
% 0.47/0.67          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.47/0.67              = (k9_relat_1 @ X2 @ (k2_relat_1 @ X3)))
% 0.47/0.67          | ~ (v1_relat_1 @ X3))),
% 0.47/0.67      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.47/0.67  thf('73', plain,
% 0.47/0.67      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67          != (k1_relat_1 @ sk_A)))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('split', [status(esa)], ['66'])).
% 0.47/0.67  thf('74', plain,
% 0.47/0.67      (((((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.47/0.67           != (k1_relat_1 @ sk_A))
% 0.47/0.67         | ~ (v1_relat_1 @ sk_A)
% 0.47/0.67         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.67  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('76', plain,
% 0.47/0.67      (((((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.47/0.67           != (k1_relat_1 @ sk_A))
% 0.47/0.67         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.67  thf('77', plain,
% 0.47/0.67      (((((k9_relat_1 @ (k4_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.47/0.67           != (k1_relat_1 @ sk_A))
% 0.47/0.67         | ~ (v1_relat_1 @ sk_A)
% 0.47/0.67         | ~ (v1_funct_1 @ sk_A)
% 0.47/0.67         | ~ (v2_funct_1 @ sk_A)
% 0.47/0.67         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['71', '76'])).
% 0.47/0.67  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('79', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('80', plain, ((v2_funct_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('81', plain,
% 0.47/0.67      (((((k9_relat_1 @ (k4_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.47/0.67           != (k1_relat_1 @ sk_A))
% 0.47/0.67         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.47/0.67  thf('82', plain,
% 0.47/0.67      (((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.47/0.67         | ~ (v1_relat_1 @ sk_A)
% 0.47/0.67         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['70', '81'])).
% 0.47/0.67  thf('83', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('84', plain,
% 0.47/0.67      (((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.47/0.67         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.67  thf('85', plain,
% 0.47/0.67      (((~ (v1_relat_1 @ sk_A)
% 0.47/0.67         | ~ (v1_funct_1 @ sk_A)
% 0.47/0.67         | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['69', '84'])).
% 0.47/0.67  thf('86', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('87', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('88', plain,
% 0.47/0.67      ((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A)))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.47/0.67  thf('89', plain,
% 0.47/0.67      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A)))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['68', '88'])).
% 0.47/0.67  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('91', plain,
% 0.47/0.67      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67                = (k1_relat_1 @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['89', '90'])).
% 0.47/0.67  thf('92', plain,
% 0.47/0.67      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67          = (k1_relat_1 @ sk_A)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['91'])).
% 0.47/0.67  thf('93', plain,
% 0.47/0.67      (~
% 0.47/0.67       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67          = (k1_relat_1 @ sk_A))) | 
% 0.47/0.67       ~
% 0.47/0.67       (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67          = (k1_relat_1 @ sk_A)))),
% 0.47/0.67      inference('split', [status(esa)], ['66'])).
% 0.47/0.67  thf('94', plain,
% 0.47/0.67      (~
% 0.47/0.67       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67          = (k1_relat_1 @ sk_A)))),
% 0.47/0.67      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.47/0.67  thf('95', plain,
% 0.47/0.67      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.47/0.67         != (k1_relat_1 @ sk_A))),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['67', '94'])).
% 0.47/0.67  thf('96', plain,
% 0.47/0.67      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_A)
% 0.47/0.67        | ~ (v1_funct_1 @ sk_A)
% 0.47/0.67        | ~ (v2_funct_1 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['65', '95'])).
% 0.47/0.67  thf('97', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('98', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('99', plain, ((v2_funct_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('100', plain, (((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 0.47/0.67  thf('101', plain, ($false), inference('simplify', [status(thm)], ['100'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
