%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.if1FhpBF8C

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:25 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 177 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   38
%              Number of atoms          : 1234 (2157 expanded)
%              Number of equality atoms :   71 ( 144 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('5',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('7',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('10',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('11',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ X11 @ ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('14',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

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

thf('56',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('71',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['56'])).

thf('72',plain,
    ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['56'])).

thf('85',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['62','85'])).

thf('87',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    $false ),
    inference(simplify,[status(thm)],['91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.if1FhpBF8C
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 168 iterations in 0.145s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.42/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.42/0.60  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.42/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(dt_k4_relat_1, axiom,
% 0.42/0.60    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.42/0.60  thf(t55_funct_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.60       ( ( v2_funct_1 @ A ) =>
% 0.42/0.60         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.42/0.60           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X13 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X13)
% 0.42/0.60          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 0.42/0.60          | ~ (v1_funct_1 @ X13)
% 0.42/0.60          | ~ (v1_relat_1 @ X13))),
% 0.42/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.42/0.60  thf(d9_funct_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.60       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X12 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X12)
% 0.42/0.60          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.42/0.60          | ~ (v1_funct_1 @ X12)
% 0.42/0.60          | ~ (v1_relat_1 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X12 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X12)
% 0.42/0.60          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.42/0.60          | ~ (v1_funct_1 @ X12)
% 0.42/0.60          | ~ (v1_relat_1 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X12 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X12)
% 0.42/0.60          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.42/0.60          | ~ (v1_funct_1 @ X12)
% 0.42/0.60          | ~ (v1_relat_1 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.42/0.60  thf(t37_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.42/0.60         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X2 : $i]:
% 0.42/0.60         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 0.42/0.60          | ~ (v1_relat_1 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X12 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X12)
% 0.42/0.60          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.42/0.60          | ~ (v1_funct_1 @ X12)
% 0.42/0.60          | ~ (v1_relat_1 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X13 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X13)
% 0.42/0.60          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 0.42/0.60          | ~ (v1_funct_1 @ X13)
% 0.42/0.60          | ~ (v1_relat_1 @ X13))),
% 0.42/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.42/0.60  thf(t80_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X11 : $i]:
% 0.42/0.60         (((k5_relat_1 @ X11 @ (k6_relat_1 @ (k2_relat_1 @ X11))) = (X11))
% 0.42/0.60          | ~ (v1_relat_1 @ X11))),
% 0.42/0.60      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X2 : $i]:
% 0.42/0.60         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 0.42/0.60          | ~ (v1_relat_1 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.42/0.60  thf(t44_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( v1_relat_1 @ B ) =>
% 0.42/0.60           ( r1_tarski @
% 0.42/0.60             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X3)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X4 @ X3)) @ 
% 0.42/0.60             (k1_relat_1 @ X4))
% 0.42/0.60          | ~ (v1_relat_1 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1)) @ 
% 0.42/0.60           (k2_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X1))),
% 0.42/0.60      inference('sup+', [status(thm)], ['14', '15'])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X1)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ 
% 0.42/0.60             (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1)) @ 
% 0.42/0.60             (k2_relat_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['13', '16'])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1)) @ 
% 0.42/0.60           (k2_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X1)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['12', '18'])).
% 0.42/0.60  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.42/0.60  thf('20', plain, (![X1 : $i]: (v1_relat_1 @ (k6_relat_1 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.42/0.60      inference('clc', [status(thm)], ['21', '22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.42/0.60           (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['11', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.42/0.60             (k1_relat_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '24'])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.42/0.60           (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.42/0.60             (k1_relat_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['9', '26'])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.42/0.60           (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['8', '28'])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '29'])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['30'])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '31'])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.42/0.60  thf(t46_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( v1_relat_1 @ B ) =>
% 0.42/0.60           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.60             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X5)
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) = (k1_relat_1 @ X6))
% 0.42/0.60          | ~ (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X5))
% 0.42/0.60          | ~ (v1_relat_1 @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.42/0.60              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.42/0.60            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['35'])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.42/0.60              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['5', '36'])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.42/0.60            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.42/0.60              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '38'])).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.42/0.60            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['39'])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.42/0.60            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['3', '40'])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.42/0.60              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.42/0.60      inference('simplify', [status(thm)], ['41'])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      (![X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X3)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X4 @ X3)) @ 
% 0.42/0.60             (k1_relat_1 @ X4))
% 0.42/0.60          | ~ (v1_relat_1 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.42/0.60  thf('44', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.42/0.60           (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.60  thf('45', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.42/0.60             (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.42/0.60      inference('simplify', [status(thm)], ['44'])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.42/0.60             (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['2', '45'])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.42/0.60             (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.42/0.60  thf('48', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['1', '47'])).
% 0.42/0.60  thf('49', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.42/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.42/0.60  thf('50', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X5)
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) = (k1_relat_1 @ X6))
% 0.42/0.60          | ~ (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X5))
% 0.42/0.60          | ~ (v1_relat_1 @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.42/0.60              = (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.42/0.60              = (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['51'])).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.42/0.60              = (k1_relat_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['0', '52'])).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.42/0.60            = (k1_relat_1 @ X0))
% 0.42/0.60          | ~ (v2_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.42/0.60  thf('55', plain,
% 0.42/0.60      (![X12 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X12)
% 0.42/0.60          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.42/0.60          | ~ (v1_funct_1 @ X12)
% 0.42/0.60          | ~ (v1_relat_1 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.42/0.60  thf(t58_funct_1, conjecture,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.60       ( ( v2_funct_1 @ A ) =>
% 0.42/0.60         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.42/0.60             ( k1_relat_1 @ A ) ) & 
% 0.42/0.60           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.42/0.60             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]:
% 0.42/0.60        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.60          ( ( v2_funct_1 @ A ) =>
% 0.42/0.60            ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.42/0.60                ( k1_relat_1 @ A ) ) & 
% 0.42/0.60              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.42/0.60                ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t58_funct_1])).
% 0.42/0.60  thf('56', plain,
% 0.42/0.60      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60          != (k1_relat_1 @ sk_A))
% 0.42/0.60        | ((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60            != (k1_relat_1 @ sk_A)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('57', plain,
% 0.42/0.60      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60          != (k1_relat_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('split', [status(esa)], ['56'])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      (((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.42/0.60           != (k1_relat_1 @ sk_A))
% 0.42/0.60         | ~ (v1_relat_1 @ sk_A)
% 0.42/0.60         | ~ (v1_funct_1 @ sk_A)
% 0.42/0.60         | ~ (v2_funct_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['55', '57'])).
% 0.42/0.60  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('60', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('61', plain, ((v2_funct_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.42/0.60          != (k1_relat_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      (![X2 : $i]:
% 0.42/0.60         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.42/0.60          | ~ (v1_relat_1 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.42/0.60  thf('64', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.42/0.60      inference('clc', [status(thm)], ['21', '22'])).
% 0.42/0.60  thf(t47_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( v1_relat_1 @ B ) =>
% 0.42/0.60           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.42/0.60             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.60  thf('65', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X7)
% 0.42/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X8)) = (k2_relat_1 @ X8))
% 0.42/0.60          | ~ (r1_tarski @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X7))
% 0.42/0.60          | ~ (v1_relat_1 @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.42/0.60  thf('66', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.42/0.60              = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.60  thf('67', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.42/0.60            = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.42/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['66'])).
% 0.42/0.60  thf('68', plain,
% 0.42/0.60      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.42/0.60  thf('69', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.42/0.60              = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.42/0.60      inference('clc', [status(thm)], ['67', '68'])).
% 0.42/0.60  thf('70', plain,
% 0.42/0.60      (![X12 : $i]:
% 0.42/0.60         (~ (v2_funct_1 @ X12)
% 0.42/0.60          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.42/0.60          | ~ (v1_funct_1 @ X12)
% 0.42/0.60          | ~ (v1_relat_1 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.42/0.60  thf('71', plain,
% 0.42/0.60      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60          != (k1_relat_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('split', [status(esa)], ['56'])).
% 0.42/0.60  thf('72', plain,
% 0.42/0.60      (((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.42/0.60           != (k1_relat_1 @ sk_A))
% 0.42/0.60         | ~ (v1_relat_1 @ sk_A)
% 0.42/0.60         | ~ (v1_funct_1 @ sk_A)
% 0.42/0.60         | ~ (v2_funct_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.60  thf('73', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('74', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('75', plain, ((v2_funct_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('76', plain,
% 0.42/0.60      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.42/0.60          != (k1_relat_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.42/0.60  thf('77', plain,
% 0.42/0.60      (((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.42/0.60         | ~ (v1_relat_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['69', '76'])).
% 0.42/0.60  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('79', plain,
% 0.42/0.60      ((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('demod', [status(thm)], ['77', '78'])).
% 0.42/0.60  thf('80', plain,
% 0.42/0.60      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['63', '79'])).
% 0.42/0.60  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('82', plain,
% 0.42/0.60      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60                = (k1_relat_1 @ sk_A))))),
% 0.42/0.60      inference('demod', [status(thm)], ['80', '81'])).
% 0.42/0.60  thf('83', plain,
% 0.42/0.60      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60          = (k1_relat_1 @ sk_A)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['82'])).
% 0.42/0.60  thf('84', plain,
% 0.42/0.60      (~
% 0.42/0.60       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60          = (k1_relat_1 @ sk_A))) | 
% 0.42/0.60       ~
% 0.42/0.60       (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60          = (k1_relat_1 @ sk_A)))),
% 0.42/0.60      inference('split', [status(esa)], ['56'])).
% 0.42/0.60  thf('85', plain,
% 0.42/0.60      (~
% 0.42/0.60       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.42/0.60          = (k1_relat_1 @ sk_A)))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.42/0.60  thf('86', plain,
% 0.42/0.60      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.42/0.60         != (k1_relat_1 @ sk_A))),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['62', '85'])).
% 0.42/0.60  thf('87', plain,
% 0.42/0.60      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.42/0.60        | ~ (v1_relat_1 @ sk_A)
% 0.42/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.42/0.60        | ~ (v2_funct_1 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['54', '86'])).
% 0.42/0.60  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('89', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('90', plain, ((v2_funct_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('91', plain, (((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.42/0.60  thf('92', plain, ($false), inference('simplify', [status(thm)], ['91'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
